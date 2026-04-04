// AletheiaClient — orchestrates backend + JSON serialization/parsing.
#include <aletheia/client.hpp>
#include <aletheia/enrich.hpp>

#include "detail/json.hpp"

#include <cmath>
#include <cstdint>
#include <cstring>
#include <format>
#include <set>
#include <string>
#include <variant>

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

// Convert a double signal value to an exact rational (numerator/denominator).
// Uses 10^9 scaling: round(value * 1e9) as numerator, 1'000'000'000 as denominator.
constexpr std::int64_t rational_denominator = 1'000'000'000;

auto to_rational_numerator(double value) -> std::int64_t {
    return static_cast<std::int64_t>(std::llround(value * static_cast<double>(rational_denominator)));
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
    , state_(std::exchange(other.state_, nullptr))
    , logger_(std::move(other.logger_))
    , diags_(std::move(other.diags_))
    , cache_(std::move(other.cache_))
    , last_frames_(std::move(other.last_frames_))
    , signal_index_(std::move(other.signal_index_)) {
}

AletheiaClient& AletheiaClient::operator=(AletheiaClient&& other) noexcept {
    if (this != &other) {
        if (backend_ != nullptr && state_ != nullptr)
            backend_->close(state_);
        backend_ = std::move(other.backend_);
        state_ = std::exchange(other.state_, nullptr);
        logger_ = std::move(other.logger_);
        diags_ = std::move(other.diags_);
        cache_ = std::move(other.cache_);
        last_frames_ = std::move(other.last_frames_);
        signal_index_ = std::move(other.signal_index_);
    }
    return *this;
}

// ---------------------------------------------------------------------------
// DBC
// ---------------------------------------------------------------------------

auto AletheiaClient::parse_dbc(const DbcDefinition& dbc) -> Result<void> {
    auto cmd = detail::serialize_parse_dbc(dbc);
    auto resp = backend_->process(state_, cmd);
    auto result = detail::parse_success(resp);
    if (result.has_value()) {
        // Populate signal name → index cache from the DBC definition.
        signal_index_.clear();
        signal_names_.clear();
        for (const auto& msg : dbc.messages) {
            auto id_value =
                std::visit([](const auto& v) -> std::uint32_t { return v.value(); }, msg.id);
            auto is_extended = std::holds_alternative<ExtendedId>(msg.id);
            std::vector<std::string> names;
            names.reserve(msg.signals.size());
            for (std::uint32_t i = 0; i < static_cast<std::uint32_t>(msg.signals.size()); ++i) {
                signal_index_.emplace(
                    SignalKey{id_value, is_extended, msg.signals[i].name.get()}, i);
                names.emplace_back(msg.signals[i].name.get());
            }
            signal_names_.emplace(MessageKey{id_value, is_extended}, std::move(names));
        }
    }
    return result;
}

auto AletheiaClient::validate_dbc(const DbcDefinition& dbc) -> Result<ValidationResult> {
    auto cmd = detail::serialize_validate_dbc(dbc);
    auto resp = backend_->process(state_, cmd);
    return detail::parse_validation(resp);
}

auto AletheiaClient::format_dbc() -> Result<DbcDefinition> {
    auto resp = backend_->format_dbc_binary(state_);
    return detail::parse_dbc_response(resp);
}

// ---------------------------------------------------------------------------
// Signals
// ---------------------------------------------------------------------------

// Error code → message mapping for binary extraction (must match Agda categorizeIndexed).
constexpr std::array extraction_error_messages = {
    std::string_view{"Signal not found in DBC"},  // 0
    std::string_view{"Value out of bounds"},       // 1
    std::string_view{"Extraction failed"},         // 2
};

auto parse_extraction_bin(std::span<const std::byte> buf,
                          const std::vector<std::string>& names) -> ExtractionResult {
    auto read_u16 = [&](std::size_t off) -> std::uint16_t {
        std::uint16_t v;
        std::memcpy(&v, buf.data() + off, sizeof(v));
        return v;
    };
    auto read_i64 = [&](std::size_t off) -> std::int64_t {
        std::int64_t v;
        std::memcpy(&v, buf.data() + off, sizeof(v));
        return v;
    };

    const auto nvals = read_u16(0);
    const auto nerrs = read_u16(2);
    const auto nabss = read_u16(4);
    std::size_t off = 6;

    ExtractionResult result;
    result.values.reserve(nvals);
    for (std::uint16_t i = 0; i < nvals; ++i) {
        auto idx = read_u16(off);
        auto num = read_i64(off + 2);
        auto den = read_i64(off + 10);
        off += 18;
        auto name = idx < names.size() ? SignalName{names[idx]} : SignalName{std::format("signal_{}", idx)};
        auto value = den != 0 ? PhysicalValue{static_cast<double>(num) / static_cast<double>(den)}
                              : PhysicalValue{0.0};
        result.values.push_back(SignalValue{std::move(name), value});
    }
    result.errors.reserve(nerrs);
    for (std::uint16_t i = 0; i < nerrs; ++i) {
        auto idx = read_u16(off);
        auto code = static_cast<std::uint8_t>(buf[off + 2]);
        off += 3;
        auto name = idx < names.size() ? SignalName{names[idx]} : SignalName{std::format("signal_{}", idx)};
        auto msg = code < extraction_error_messages.size()
                       ? std::string{extraction_error_messages[code]}
                       : std::format("Unknown error code {}", code);
        result.errors.emplace_back(std::move(name), std::move(msg));
    }
    result.absent.reserve(nabss);
    for (std::uint16_t i = 0; i < nabss; ++i) {
        auto idx = read_u16(off);
        off += 2;
        auto name = idx < names.size() ? SignalName{names[idx]} : SignalName{std::format("signal_{}", idx)};
        result.absent.push_back(std::move(name));
    }
    return result;
}

auto AletheiaClient::extract_signals(CanId id, Dlc dlc, std::span<const std::byte> data)
    -> Result<ExtractionResult> {
    if (auto v = validate_payload(dlc, data); !v.has_value())
        return std::unexpected(v.error());

    // Use binary path when signal name cache is populated.
    auto id_value = std::visit([](const auto& v) -> std::uint32_t { return v.value(); }, id);
    auto is_extended = std::holds_alternative<ExtendedId>(id);
    auto names_it = signal_names_.find(MessageKey{id_value, is_extended});
    if (names_it != signal_names_.end()) {
        auto buf = backend_->extract_signals_bin(state_, id, dlc, data);
        if (!buf)
            return std::unexpected(buf.error());
        return parse_extraction_bin(*buf, names_it->second);
    }

    // Fallback: JSON path.
    auto resp = backend_->extract_signals_binary(state_, id, dlc, data);
    return detail::parse_extraction(resp);
}

auto AletheiaClient::build_frame(CanId id, Dlc dlc, std::span<const SignalValue> signals)
    -> Result<FramePayload> {
    // Use binary FFI path when signal index cache is populated.
    if (!signal_index_.empty()) {
        auto id_value =
            std::visit([](const auto& v) -> std::uint32_t { return v.value(); }, id);
        auto is_extended = std::holds_alternative<ExtendedId>(id);

        std::vector<std::uint32_t> indices;
        std::vector<std::int64_t> numerators;
        std::vector<std::int64_t> denominators;
        indices.reserve(signals.size());
        numerators.reserve(signals.size());
        denominators.reserve(signals.size());

        for (const auto& sv : signals) {
            auto it = signal_index_.find(
                SignalKey{id_value, is_extended, sv.name.get()});
            if (it == signal_index_.end()) {
                return std::unexpected(
                    AletheiaError{ErrorKind::Validation,
                                  std::format("signal '{}' not found in DBC for CAN ID {}",
                                              std::string_view{sv.name}, id_value)});
            }
            indices.push_back(it->second);
            numerators.push_back(to_rational_numerator(sv.value.get()));
            denominators.push_back(rational_denominator);
        }

        return backend_->build_frame_bin(
            state_, id, dlc, static_cast<std::uint32_t>(signals.size()), indices.data(),
            numerators.data(), denominators.data(), dlc_to_bytes(dlc));
    }
    // Fallback: JSON serialization (MockBackend, or no DBC loaded).
    auto cmd = detail::serialize_build_frame(id, dlc, signals);
    auto resp = backend_->process(state_, cmd);
    return detail::parse_frame_data(resp);
}

auto AletheiaClient::update_frame(CanId id, Dlc dlc, std::span<const std::byte> data,
                                  std::span<const SignalValue> signals) -> Result<FramePayload> {
    if (auto v = validate_payload(dlc, data); !v.has_value())
        return std::unexpected(v.error());
    // Use binary FFI path when signal index cache is populated.
    if (!signal_index_.empty()) {
        auto id_value =
            std::visit([](const auto& v) -> std::uint32_t { return v.value(); }, id);
        auto is_extended = std::holds_alternative<ExtendedId>(id);

        std::vector<std::uint32_t> indices;
        std::vector<std::int64_t> numerators;
        std::vector<std::int64_t> denominators;
        indices.reserve(signals.size());
        numerators.reserve(signals.size());
        denominators.reserve(signals.size());

        for (const auto& sv : signals) {
            auto it = signal_index_.find(
                SignalKey{id_value, is_extended, sv.name.get()});
            if (it == signal_index_.end()) {
                return std::unexpected(
                    AletheiaError{ErrorKind::Validation,
                                  std::format("signal '{}' not found in DBC for CAN ID {}",
                                              std::string_view{sv.name}, id_value)});
            }
            indices.push_back(it->second);
            numerators.push_back(to_rational_numerator(sv.value.get()));
            denominators.push_back(rational_denominator);
        }

        return backend_->update_frame_bin(
            state_, id, dlc, data, static_cast<std::uint32_t>(signals.size()), indices.data(),
            numerators.data(), denominators.data(), dlc_to_bytes(dlc));
    }
    // Fallback: JSON serialization (MockBackend, or no DBC loaded).
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
    auto resp = backend_->start_stream_binary(state_);
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

auto AletheiaClient::send_frames(std::span<const Frame> frames) -> BatchResult {
    BatchResult batch;
    batch.responses.reserve(frames.size());
    for (const auto& f : frames) {
        auto r = send_frame(f.timestamp, f.id, f.dlc,
                            std::span<const std::byte>(f.data.data(), f.data.size()));
        if (!r.has_value()) {
            batch.error = r.error();
            return batch;
        }
        batch.responses.push_back(std::move(*r));
    }
    return batch;
}

auto AletheiaClient::end_stream() -> Result<StreamResult> {
    auto resp = backend_->end_stream_binary(state_);
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

auto collect_matching_signals(const PropertyDiagnostic& diag, const ExtractionResult& extraction)
    -> std::map<SignalName, PhysicalValue> {
    std::map<SignalName, PhysicalValue> values;
    for (const auto& sig : diag.signals) {
        for (const auto& sv : extraction.values) {
            if (sv.name == sig) {
                values.emplace(sig, sv.value);
                break;
            }
        }
    }
    return values;
}

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
        // Property index out of range — protocol mismatch; skip enrichment.
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
        // Property index out of range — protocol mismatch; skip enrichment.
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
    const FramePayload payload(data.begin(), data.end());
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
        if (cache_.size() < max_cache_size) {
            cache_it = cache_.emplace(key, std::move(*extraction)).first;
        } else {
            if (logger_)
                logger_.warn("cache.full", {{"size", static_cast<std::int64_t>(cache_.size())}});
            // Over capacity — use result directly without caching
            return collect_matching_signals(diag, *extraction);
        }
    } else if (logger_) {
        logger_.debug("cache.hit", {{"canId", static_cast<std::uint64_t>(id_value)},
                                    {"dlc", static_cast<std::uint64_t>(dlc.value())}});
    }

    return collect_matching_signals(diag, cache_it->second);
}

auto AletheiaClient::extract_last_known_values(const PropertyDiagnostic& diag)
    -> std::map<SignalName, PhysicalValue> {
    if (last_frames_.empty() || diag.signals.empty())
        return {};
    std::set<SignalName> wanted(diag.signals.begin(), diag.signals.end());
    std::map<SignalName, PhysicalValue> values;
    for (const auto& [key, last_frame] : last_frames_) {
        auto extraction = extract_signals_internal(last_frame.id, last_frame.dlc, last_frame.data);
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
    auto is_extended = std::holds_alternative<ExtendedId>(id);

    // Use binary path when signal name cache is populated.
    auto names_it = signal_names_.find(MessageKey{id_value, is_extended});
    if (names_it != signal_names_.end()) {
        auto buf = backend_->extract_signals_bin(state_, id, dlc, data);
        if (!buf) {
            if (logger_)
                logger_.warn("extraction.process_failed",
                             {{"canId", static_cast<std::uint64_t>(id_value)},
                              {"error", buf.error().message()}});
            return std::nullopt;
        }
        return parse_extraction_bin(*buf, names_it->second);
    }

    // Fallback: JSON path.
    std::string resp;
    try {
        resp = backend_->extract_signals_binary(state_, id, dlc, data);
    } catch (const std::exception& e) {
        if (logger_)
            logger_.warn("extraction.process_failed",
                         {{"canId", static_cast<std::uint64_t>(id_value)},
                          {"error", std::string{e.what()}}});
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
