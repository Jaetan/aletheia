// AletheiaClient — orchestrates backend + JSON serialization/parsing.
#include <aletheia/client.hpp>
#include <aletheia/enrich.hpp>

#include "detail/json.hpp"

#include <array>
#include <cmath>
#include <cstddef>
#include <cstdint>
#include <cstring>
#include <exception>
#include <expected>
#include <format>
#include <limits>
#include <map>
#include <memory>
#include <optional>
#include <set>
#include <span>
#include <string>
#include <utility>
#include <variant>
#include <vector>

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
    auto scaled = value * static_cast<double>(rational_denominator);
    if (scaled < static_cast<double>(std::numeric_limits<std::int64_t>::min()) ||
        scaled > static_cast<double>(std::numeric_limits<std::int64_t>::max()))
        throw std::overflow_error("signal value too large for rational representation");
    return static_cast<std::int64_t>(std::llround(scaled));
}

} // namespace

AletheiaClient::AletheiaClient(std::unique_ptr<IBackend> backend, Logger logger,
                               std::vector<CheckResult> default_checks)
    : backend_(std::move(backend))
    , state_(backend_->init())
    , logger_(std::move(logger))
    , default_checks_(std::move(default_checks)) {
    if (auto w = backend_->pending_warning(); !w.empty() && logger_)
        logger_.warn("backend.init", {{"warning", w}});
}

AletheiaClient::~AletheiaClient() {
    if (backend_ != nullptr && state_ != nullptr) {
        try {
            backend_->close(state_);
        } catch (...) {}
    }
}

AletheiaClient::AletheiaClient(AletheiaClient&& other) noexcept
    : backend_(std::move(other.backend_))
    , state_(std::exchange(other.state_, nullptr))
    , logger_(std::move(other.logger_))
    , default_checks_(std::move(other.default_checks_))
    , diags_(std::move(other.diags_))
    , cache_(std::move(other.cache_))
    , last_frames_(std::move(other.last_frames_))
    , signal_index_(std::move(other.signal_index_))
    , signal_names_(std::move(other.signal_names_)) {
}

AletheiaClient& AletheiaClient::operator=(AletheiaClient&& other) noexcept {
    if (this != &other) {
        if (backend_ != nullptr && state_ != nullptr) {
            try {
                backend_->close(state_);
            } catch (...) {}
        }
        backend_ = std::move(other.backend_);
        state_ = std::exchange(other.state_, nullptr);
        logger_ = std::move(other.logger_);
        default_checks_ = std::move(other.default_checks_);
        diags_ = std::move(other.diags_);
        cache_ = std::move(other.cache_);
        last_frames_ = std::move(other.last_frames_);
        signal_index_ = std::move(other.signal_index_);
        signal_names_ = std::move(other.signal_names_);
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
                signal_index_.emplace(detail::SignalKey{.id_value = id_value,
                                                        .is_extended = is_extended,
                                                        .signal_name = msg.signals[i].name.get()},
                                      i);
                names.emplace_back(msg.signals[i].name.get());
            }
            signal_names_.emplace(detail::MessageKey{id_value, is_extended}, std::move(names));
        }
        if (logger_)
            logger_.info("dbc.parsed",
                         {{"messages", static_cast<std::int64_t>(dbc.messages.size())}});
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

namespace {

// Error code → message mapping for binary extraction (must match Agda categorizeIndexed).
constexpr std::array extraction_error_messages = {
    std::string_view{"Signal not found in DBC"}, // 0
    std::string_view{"Value out of bounds"},     // 1
    std::string_view{"Extraction failed"},       // 2
};

auto parse_extraction_bin(std::span<const std::byte> buf, const std::vector<std::string>& names)
    -> ExtractionResult {
    auto read_u16 = [&](std::size_t off) -> std::uint16_t {
        std::uint16_t v = 0;
        std::memcpy(&v, buf.data() + off, sizeof(v));
        return v;
    };
    auto read_i64 = [&](std::size_t off) -> std::int64_t {
        std::int64_t v = 0;
        std::memcpy(&v, buf.data() + off, sizeof(v));
        return v;
    };

    if (buf.size() < 6)
        return {};
    const auto nvals = read_u16(0);
    const auto nerrs = read_u16(2);
    const auto nabss = read_u16(4);
    const auto expected_size =
        std::size_t{6} + std::size_t{nvals} * 18 + std::size_t{nerrs} * 3 + std::size_t{nabss} * 2;
    if (buf.size() < expected_size)
        return {};
    std::size_t off = 6;

    ExtractionResult result;
    result.values.reserve(nvals);
    for (std::uint16_t i = 0; i < nvals; ++i) {
        // Per-read bounds check — redundant with the upfront expected_size
        // guard above, but keeps the loop locally defensive against future
        // changes to the record layout or header computation.
        if (off + 18 > buf.size())
            return {};
        auto idx = read_u16(off);
        auto num = read_i64(off + 2);
        auto den = read_i64(off + 10);
        off += 18;
        auto name =
            idx < names.size() ? SignalName{names[idx]} : SignalName{std::format("signal_{}", idx)};
        auto value = den != 0 ? PhysicalValue{static_cast<double>(num) / static_cast<double>(den)}
                              : PhysicalValue{0.0};
        result.values.push_back(SignalValue{.name = std::move(name), .value = value});
    }
    result.errors.reserve(nerrs);
    for (std::uint16_t i = 0; i < nerrs; ++i) {
        if (off + 3 > buf.size())
            return {};
        auto idx = read_u16(off);
        auto code = static_cast<std::uint8_t>(buf[off + 2]);
        off += 3;
        auto name =
            idx < names.size() ? SignalName{names[idx]} : SignalName{std::format("signal_{}", idx)};
        auto msg = code < extraction_error_messages.size()
                       ? std::string{extraction_error_messages[code]}
                       : std::format("Unknown error code {}", code);
        result.errors.emplace_back(std::move(name), std::move(msg));
    }
    result.absent.reserve(nabss);
    for (std::uint16_t i = 0; i < nabss; ++i) {
        if (off + 2 > buf.size())
            return {};
        auto idx = read_u16(off);
        off += 2;
        auto name =
            idx < names.size() ? SignalName{names[idx]} : SignalName{std::format("signal_{}", idx)};
        result.absent.push_back(std::move(name));
    }
    return result;
}

} // namespace

auto AletheiaClient::extract_signals(CanId id, Dlc dlc, std::span<const std::byte> data)
    -> Result<ExtractionResult> {
    if (auto v = validate_payload(dlc, data); !v.has_value())
        return std::unexpected(v.error());

    // Use binary path when signal name cache is populated.
    auto id_value = std::visit([](const auto& v) -> std::uint32_t { return v.value(); }, id);
    auto is_extended = std::holds_alternative<ExtendedId>(id);
    auto names_it = signal_names_.find(detail::MessageKey{id_value, is_extended});
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

auto AletheiaClient::ResolvedSignals::injection() const -> SignalInjection {
    return {.count = static_cast<std::uint32_t>(indices.size()),
            .indices = indices.data(),
            .numerators = numerators.data(),
            .denominators = denominators.data()};
}

auto AletheiaClient::resolve_signals(CanId id, std::span<const SignalValue> signals)
    -> Result<ResolvedSignals> {
    auto id_value = std::visit([](const auto& v) -> std::uint32_t { return v.value(); }, id);
    auto is_extended = std::holds_alternative<ExtendedId>(id);

    ResolvedSignals resolved;
    resolved.indices.reserve(signals.size());
    resolved.numerators.reserve(signals.size());
    resolved.denominators.reserve(signals.size());

    for (const auto& sv : signals) {
        auto it = signal_index_.find(detail::SignalKey{
            .id_value = id_value, .is_extended = is_extended, .signal_name = sv.name.get()});
        if (it == signal_index_.end()) {
            return std::unexpected(AletheiaError{
                ErrorKind::Validation, std::format("signal '{}' not found in DBC for CAN ID {}",
                                                   std::string_view{sv.name}, id_value)});
        }
        resolved.indices.push_back(it->second);
        resolved.numerators.push_back(to_rational_numerator(sv.value.get()));
        resolved.denominators.push_back(rational_denominator);
    }
    return resolved;
}

auto AletheiaClient::build_frame(CanId id, Dlc dlc, std::span<const SignalValue> signals)
    -> Result<FramePayload> {
    if (signal_index_.empty()) {
        return std::unexpected(
            AletheiaError{ErrorKind::State, "build_frame: no DBC loaded (call parse_dbc first)"});
    }
    auto resolved = resolve_signals(id, signals);
    if (!resolved) {
        return std::unexpected(resolved.error());
    }
    auto inj = resolved->injection();
    return backend_->build_frame_bin(state_, id, dlc, inj, dlc_to_bytes(dlc));
}

auto AletheiaClient::update_frame(CanId id, Dlc dlc, std::span<const std::byte> data,
                                  std::span<const SignalValue> signals) -> Result<FramePayload> {
    if (auto v = validate_payload(dlc, data); !v.has_value()) {
        return std::unexpected(v.error());
    }
    if (signal_index_.empty()) {
        return std::unexpected(
            AletheiaError{ErrorKind::State, "update_frame: no DBC loaded (call parse_dbc first)"});
    }
    auto resolved = resolve_signals(id, signals);
    if (!resolved) {
        return std::unexpected(resolved.error());
    }
    auto inj = resolved->injection();
    return backend_->update_frame_bin(state_, id, dlc, data, inj, dlc_to_bytes(dlc));
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
    formulas.reserve(default_checks_.size() + checks.size());
    for (const auto& dc : default_checks_) {
        const auto& f = dc.formula();
        if (f)
            formulas.push_back(ltl::clone(*f));
    }
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
        auto id_value = std::visit([](const auto& v) -> std::uint32_t { return v.value(); }, id);
        auto is_extended = std::holds_alternative<ExtendedId>(id);
        // Track last frame per CAN ID for end-of-stream enrichment (skip when no diagnostics).
        if (!diags_.empty())
            last_frames_.insert_or_assign(
                LastFrameKey{id_value, is_extended},
                LastFrame{.id = id, .dlc = dlc, .data = FramePayload(data.begin(), data.end())});
        if (auto* v = std::get_if<Violation>(&*result); v != nullptr && !diags_.empty()) {
            enrich_violation(*v, id, dlc, data, id_value, is_extended);
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

auto AletheiaClient::send_error(Timestamp ts) -> Result<void> {
    if (ts.count() < 0)
        return std::unexpected(
            AletheiaError{ErrorKind::Validation, "timestamp must be non-negative"});
    auto resp = backend_->send_error_binary(state_, ts);
    auto r = detail::parse_success(resp);
    if (r.has_value() && logger_) {
        logger_.debug("error_event.sent", {{"ts", static_cast<std::int64_t>(ts.count())},
                                           {"response", std::string_view{"ack"}}});
    }
    return r;
}

auto AletheiaClient::send_remote(Timestamp ts, CanId id) -> Result<void> {
    if (ts.count() < 0)
        return std::unexpected(
            AletheiaError{ErrorKind::Validation, "timestamp must be non-negative"});
    auto resp = backend_->send_remote_binary(state_, ts, id);
    auto r = detail::parse_success(resp);
    if (r.has_value() && logger_) {
        logger_.debug(
            "remote_event.sent",
            {{"ts", static_cast<std::int64_t>(ts.count())},
             {"canId", static_cast<std::uint64_t>(std::visit(
                           [](const auto& v) -> std::uint32_t { return v.value(); }, id))},
             {"extended", std::holds_alternative<ExtendedId>(id)},
             {"response", std::string_view{"ack"}}});
    }
    return r;
}

auto AletheiaClient::end_stream() -> Result<StreamResult> {
    auto resp = backend_->end_stream_binary(state_);
    auto result = detail::parse_stream_result(resp);
    if (result.has_value()) {
        if (!diags_.empty()) {
            for (auto& pr : result->results) {
                if (pr.verdict == Verdict::Fails || pr.verdict == Verdict::Unresolved)
                    enrich_property_result(pr);
            }
        }
        if (logger_) {
            std::int64_t num_fails = 0;
            std::int64_t num_unresolved = 0;
            for (const auto& pr : result->results) {
                if (pr.verdict == Verdict::Fails)
                    ++num_fails;
                else if (pr.verdict == Verdict::Unresolved)
                    ++num_unresolved;
            }
            logger_.info("stream.ended",
                         {{"numResults", static_cast<std::int64_t>(result->results.size())},
                          {"numFails", num_fails},
                          {"numUnresolved", num_unresolved}});
        }
        last_frames_.clear();
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
                                      std::span<const std::byte> data, std::uint32_t id_value,
                                      bool is_extended) {
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
    auto values = extract_signal_values(diag, id, dlc, data, id_value, is_extended);
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
                                           std::span<const std::byte> data, std::uint32_t id_value,
                                           bool is_extended)
    -> std::map<SignalName, PhysicalValue> {
    // Heterogeneous lookup via FrameKeyView — avoids copying the payload into
    // a FramePayload on cache hits (the common hot-path case).
    const detail::FrameKeyView lookup{
        .id_value = id_value, .is_extended = is_extended, .dlc = dlc.value(), .data = data};

    auto cache_it = cache_.find(lookup);
    if (cache_it == cache_.end()) {
        if (logger_)
            logger_.debug("cache.miss", {{"canId", static_cast<std::uint64_t>(id_value)},
                                         {"dlc", static_cast<std::uint64_t>(dlc.value())}});
        auto extraction = extract_signals_internal(id, dlc, data, id_value, is_extended);
        if (!extraction.has_value())
            return {};
        if (cache_.size() < max_cache_size) {
            // Construct the owning FrameKey only on insertion.
            detail::FrameKey key{.id_value = id_value,
                                 .is_extended = is_extended,
                                 .dlc = dlc.value(),
                                 .data = FramePayload(data.begin(), data.end())};
            cache_it = cache_.emplace(std::move(key), std::move(*extraction)).first;
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
        auto extraction = extract_signals_internal(last_frame.id, last_frame.dlc, last_frame.data,
                                                   key.first, key.second);
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

auto AletheiaClient::extract_signals_internal(CanId id, Dlc dlc, std::span<const std::byte> data,
                                              std::uint32_t id_value, bool is_extended)
    -> std::optional<ExtractionResult> {
    // Use binary path when signal name cache is populated.
    auto names_it = signal_names_.find(detail::MessageKey{id_value, is_extended});
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
                         {{"canId", static_cast<std::uint64_t>(id_value)},
                          {"error", result.error().message()}});
        return std::nullopt;
    }
    return std::move(*result);
}

} // namespace aletheia
