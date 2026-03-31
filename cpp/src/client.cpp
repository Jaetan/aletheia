// AletheiaClient — orchestrates backend + JSON serialization/parsing.
#include <aletheia/client.hpp>
#include <aletheia/enrich.hpp>

#include "detail/json.hpp"

#include <format>
#include <set>
#include <string>

namespace aletheia {

namespace {

auto validate_payload(Dlc dlc, std::span<const std::byte> data) -> Result<void> {
    auto expected = dlc_to_bytes(dlc);
    if (data.size() != expected)
        return std::unexpected(
            AletheiaError{ErrorKind::Validation,
                          std::format("payload length {} does not match DLC {} (expected {} bytes)",
                                      data.size(), dlc.value(), expected)});
    return {};
}

} // namespace

AletheiaClient::AletheiaClient(std::unique_ptr<IBackend> backend, Logger logger)
    : backend_(std::move(backend))
    , state_(backend_->init())
    , logger_(std::move(logger)) {
}

AletheiaClient::~AletheiaClient() {
    if (backend_ != nullptr && state_ != nullptr)
        backend_->close(state_);
}

AletheiaClient::AletheiaClient(AletheiaClient&& other) noexcept
    : backend_(std::move(other.backend_))
    , state_(std::exchange(other.state_, nullptr)) {
}

AletheiaClient& AletheiaClient::operator=(AletheiaClient&& other) noexcept {
    if (this != &other) {
        if (backend_ != nullptr && state_ != nullptr)
            backend_->close(state_);
        backend_ = std::move(other.backend_);
        state_ = std::exchange(other.state_, nullptr);
    }
    return *this;
}

// ---------------------------------------------------------------------------
// DBC
// ---------------------------------------------------------------------------

auto AletheiaClient::parse_dbc(const DbcDefinition& dbc) -> Result<void> {
    auto cmd = detail::serialize_parse_dbc(dbc);
    auto resp = backend_->process(state_, cmd);
    return detail::parse_success(resp);
}

auto AletheiaClient::validate_dbc(const DbcDefinition& dbc) -> Result<ValidationResult> {
    auto cmd = detail::serialize_validate_dbc(dbc);
    auto resp = backend_->process(state_, cmd);
    return detail::parse_validation(resp);
}

auto AletheiaClient::format_dbc() -> Result<DbcDefinition> {
    auto cmd = detail::serialize_format_dbc();
    auto resp = backend_->process(state_, cmd);
    return detail::parse_dbc_response(resp);
}

// ---------------------------------------------------------------------------
// Signals
// ---------------------------------------------------------------------------

auto AletheiaClient::extract_signals(CanId id, Dlc dlc, std::span<const std::byte> data)
    -> Result<ExtractionResult> {
    if (auto v = validate_payload(dlc, data); !v.has_value())
        return std::unexpected(v.error());
    auto cmd = detail::serialize_extract_signals(id, dlc, data);
    auto resp = backend_->process(state_, cmd);
    return detail::parse_extraction(resp);
}

auto AletheiaClient::build_frame(CanId id, Dlc dlc, std::span<const SignalValue> signals)
    -> Result<FramePayload> {
    auto cmd = detail::serialize_build_frame(id, dlc, signals);
    auto resp = backend_->process(state_, cmd);
    return detail::parse_frame_data(resp);
}

auto AletheiaClient::update_frame(CanId id, Dlc dlc, std::span<const std::byte> data,
                                  std::span<const SignalValue> signals) -> Result<FramePayload> {
    if (auto v = validate_payload(dlc, data); !v.has_value())
        return std::unexpected(v.error());
    auto cmd = detail::serialize_update_frame(id, dlc, data, signals);
    auto resp = backend_->process(state_, cmd);
    return detail::parse_frame_data(resp);
}

// ---------------------------------------------------------------------------
// Streaming
// ---------------------------------------------------------------------------

auto AletheiaClient::set_properties(std::span<const LtlFormula> properties) -> Result<void> {
    auto cmd = detail::serialize_set_properties(properties);
    auto resp = backend_->process(state_, cmd);
    auto result = detail::parse_success(resp);
    if (!result.has_value())
        return result;
    diags_.clear();
    diags_.reserve(properties.size());
    for (const auto& f : properties)
        diags_.push_back(build_diagnostic(f));
    cache_.clear();
    if (logger_)
        logger_.info("properties.set", {{"count", static_cast<std::int64_t>(properties.size())}});
    return result;
}

auto AletheiaClient::add_checks(std::vector<CheckResult> checks) -> Result<void> {
    std::vector<LtlFormula> formulas;
    formulas.reserve(checks.size());
    for (auto& check : checks) {
        auto f = check.to_formula();
        if (!f)
            return std::unexpected(
                AletheiaError{ErrorKind::Validation, "check has no formula (already consumed)"});
        formulas.push_back(std::move(*f));
    }
    return set_properties(formulas);
}

auto AletheiaClient::start_stream() -> Result<void> {
    auto cmd = detail::serialize_start_stream();
    auto resp = backend_->process(state_, cmd);
    auto result = detail::parse_success(resp);
    if (result.has_value()) {
        cache_.clear();
        last_frames_.clear();
        if (logger_)
            logger_.info("stream.started");
    }
    return result;
}

auto AletheiaClient::send_frame(Timestamp ts, CanId id, Dlc dlc, std::span<const std::byte> data)
    -> Result<FrameResponse> {
    if (ts.count() < 0)
        return std::unexpected(
            AletheiaError{ErrorKind::Validation, "timestamp must be non-negative"});
    if (auto v = validate_payload(dlc, data); !v.has_value())
        return std::unexpected(v.error());
    auto resp = backend_->send_frame_binary(state_, ts, id, dlc, data);
    auto result = detail::parse_frame_response(resp);
    if (result.has_value()) {
        // Track last frame per CAN ID for end-of-stream enrichment.
        auto id_value = std::visit([](const auto& v) -> std::uint32_t { return v.value(); }, id);
        auto is_extended = std::holds_alternative<ExtendedId>(id);
        last_frames_.insert_or_assign(
            LastFrameKey{id_value, is_extended},
            LastFrame{.id = id, .dlc = dlc, .data = FramePayload(data.begin(), data.end())});
        if (auto* v = std::get_if<Violation>(&*result); v != nullptr && !diags_.empty()) {
            enrich_violation(*v, id, dlc, data);
            if (logger_)
                logger_.debug("frame.processed", {{"ts", static_cast<std::int64_t>(ts.count())},
                                                  {"canId", static_cast<std::uint64_t>(id_value)},
                                                  {"extended", is_extended},
                                                  {"response", std::string_view{"violation"}}});
        } else if (logger_) {
            logger_.debug("frame.processed", {{"ts", static_cast<std::int64_t>(ts.count())},
                                              {"canId", static_cast<std::uint64_t>(id_value)},
                                              {"extended", is_extended},
                                              {"response", std::string_view{"ack"}}});
        }
    }
    return result;
}

auto AletheiaClient::end_stream() -> Result<StreamResult> {
    auto cmd = detail::serialize_end_stream();
    auto resp = backend_->process(state_, cmd);
    auto result = detail::parse_stream_result(resp);
    if (result.has_value()) {
        if (!diags_.empty()) {
            for (auto& pr : result->results) {
                if (pr.verdict == Verdict::Fails)
                    enrich_property_result(pr);
            }
        }
        if (logger_) {
            std::int64_t num_fails = 0;
            for (const auto& pr : result->results) {
                if (pr.verdict == Verdict::Fails)
                    ++num_fails;
            }
            logger_.info("stream.ended",
                         {{"numResults", static_cast<std::int64_t>(result->results.size())},
                          {"numFails", num_fails}});
        }
    }
    return result;
}

// ---------------------------------------------------------------------------
// Enrichment internals
// ---------------------------------------------------------------------------

namespace {

auto format_enriched_reason(const PropertyDiagnostic& diag,
                            const std::map<SignalName, PhysicalValue>& values,
                            std::string_view core_reason) -> std::string {
    std::string reason;
    if (values.empty()) {
        reason = "violated: " + diag.formula_desc;
    } else {
        bool first = true;
        for (const auto& sig : diag.signals) {
            if (auto it = values.find(sig); it != values.end()) {
                if (!first)
                    reason += ", ";
                reason += std::format("{} = {:g}", std::string_view{sig}, it->second.get());
                first = false;
            }
        }
        if (first) {
            reason = "violated: " + diag.formula_desc;
        } else {
            reason += " (formula: " + diag.formula_desc + ")";
        }
    }
    if (!core_reason.empty())
        reason += " [core: " + std::string{core_reason} + "]";
    return reason;
}

} // namespace

void AletheiaClient::enrich_violation(Violation& v, CanId id, Dlc dlc,
                                      std::span<const std::byte> data) {
    auto idx = v.property_index.get();
    if (idx >= diags_.size()) {
        if (logger_)
            logger_.warn("enrichment.property_index_oob",
                         {{"index", static_cast<std::int64_t>(idx)},
                          {"count", static_cast<std::int64_t>(diags_.size())}});
        return;
    }
    const auto& diag = diags_[idx];
    auto values = extract_signal_values(diag, id, dlc, data);
    auto reason = format_enriched_reason(diag, values, v.reason);
    v.enrichment = ViolationEnrichment{
        .signals = std::move(values),
        .formula_desc = diag.formula_desc,
        .enriched_reason = std::move(reason),
        .core_reason = v.reason,
    };
}

void AletheiaClient::enrich_property_result(PropertyResult& pr) {
    auto idx = pr.property_index.get();
    if (idx >= diags_.size()) {
        if (logger_)
            logger_.warn("enrichment.property_index_oob",
                         {{"index", static_cast<std::int64_t>(idx)},
                          {"count", static_cast<std::int64_t>(diags_.size())}});
        return;
    }
    const auto& diag = diags_[idx];
    auto values = extract_last_known_values(diag);
    auto reason = format_enriched_reason(diag, values, pr.reason);
    pr.enrichment = ViolationEnrichment{
        .signals = std::move(values),
        .formula_desc = diag.formula_desc,
        .enriched_reason = std::move(reason),
        .core_reason = pr.reason,
    };
}

auto AletheiaClient::extract_signal_values(const PropertyDiagnostic& diag, CanId id, Dlc dlc,
                                           std::span<const std::byte> data)
    -> std::map<SignalName, PhysicalValue> {
    auto id_value = std::visit([](const auto& v) -> std::uint32_t { return v.value(); }, id);
    auto is_extended = std::holds_alternative<ExtendedId>(id);
    FramePayload payload(data.begin(), data.end());
    FrameKey key{
        .id_value = id_value, .is_extended = is_extended, .dlc = dlc.value(), .data = payload};

    auto cache_it = cache_.find(key);
    if (cache_it == cache_.end()) {
        if (logger_)
            logger_.debug("cache.miss", {{"canId", static_cast<std::uint64_t>(id_value)},
                                         {"dlc", static_cast<std::uint64_t>(dlc.value())}});
        auto extraction = extract_signals_internal(id, dlc, data);
        if (!extraction.has_value())
            return {};
        if (cache_.size() < max_cache_size_) {
            cache_it = cache_.emplace(key, std::move(*extraction)).first;
        } else {
            if (logger_)
                logger_.warn("cache.full", {{"size", static_cast<std::int64_t>(cache_.size())}});
            // Over capacity — use result directly without caching
            std::map<SignalName, PhysicalValue> values;
            for (const auto& sig : diag.signals) {
                for (const auto& sv : extraction->values) {
                    if (sv.name == sig) {
                        values.emplace(sig, sv.value);
                        break;
                    }
                }
            }
            return values;
        }
    } else if (logger_) {
        logger_.debug("cache.hit", {{"canId", static_cast<std::uint64_t>(id_value)},
                                    {"dlc", static_cast<std::uint64_t>(dlc.value())}});
    }

    std::map<SignalName, PhysicalValue> values;
    for (const auto& sig : diag.signals) {
        for (const auto& sv : cache_it->second.values) {
            if (sv.name == sig) {
                values.emplace(sig, sv.value);
                break;
            }
        }
    }
    return values;
}

auto AletheiaClient::extract_last_known_values(const PropertyDiagnostic& diag)
    -> std::map<SignalName, PhysicalValue> {
    if (last_frames_.empty() || diag.signals.empty())
        return {};
    std::set<SignalName> wanted(diag.signals.begin(), diag.signals.end());
    std::map<SignalName, PhysicalValue> values;
    for (const auto& [key, lf] : last_frames_) {
        auto extraction = extract_signals_internal(lf.id, lf.dlc, lf.data);
        if (!extraction.has_value()) {
            if (logger_)
                logger_.warn("enrichment.extraction_failed",
                             {{"canId", static_cast<std::uint64_t>(key.first)}});
            continue;
        }
        for (const auto& sv : extraction->values) {
            if (wanted.contains(sv.name)) {
                values.insert_or_assign(sv.name, sv.value);
                wanted.erase(sv.name);
            }
        }
        if (wanted.empty())
            break;
    }
    return values;
}

auto AletheiaClient::extract_signals_internal(CanId id, Dlc dlc, std::span<const std::byte> data)
    -> std::optional<ExtractionResult> {
    auto id_value = std::visit([](const auto& v) -> std::uint32_t { return v.value(); }, id);
    std::string cmd;
    try {
        cmd = detail::serialize_extract_signals(id, dlc, data);
    } catch (...) {
        if (logger_)
            logger_.warn("extraction.serialize_failed",
                         {{"canId", static_cast<std::uint64_t>(id_value)}});
        return std::nullopt;
    }
    std::string resp;
    try {
        resp = backend_->process(state_, cmd);
    } catch (...) {
        if (logger_)
            logger_.warn("extraction.process_failed",
                         {{"canId", static_cast<std::uint64_t>(id_value)}});
        return std::nullopt;
    }
    auto result = detail::parse_extraction(resp);
    if (!result.has_value()) {
        if (logger_)
            logger_.warn("extraction.parse_failed",
                         {{"canId", static_cast<std::uint64_t>(id_value)}});
        return std::nullopt;
    }
    return std::move(*result);
}

} // namespace aletheia
