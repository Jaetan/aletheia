// SPDX-FileCopyrightText: 2025 Nicolas Pelletier
// SPDX-License-Identifier: BSD-2-Clause
// AletheiaClient — orchestrates backend + JSON serialization/parsing.
#include <aletheia/client.hpp>
#include <aletheia/detail/cache_keys.hpp>
#include <aletheia/detail/rational_renderer.hpp>
#include <aletheia/enrich.hpp>
#include <aletheia/limits.hpp>

#include "detail/json.hpp"

#include <array>
#include <bit>
#include <cstddef>
#include <cstdint>
#include <cstring>
#include <exception>
#include <expected>
#include <format>
#include <map>
#include <memory>
#include <optional>
#include <set>
#include <span>
#include <stop_token>
#include <string>
#include <string_view>
#include <utility>
#include <variant>
#include <vector>

// parse_extraction_bin uses std::memcpy reads
// in native byte order (per the wire-format note at AletheiaFFI.hs:235).
// On a big-endian host the same memcpy would silently misinterpret the
// bytes; refuse to compile rather than ship an architecture-dependent ABI.
static_assert(std::endian::native == std::endian::little,
              "Aletheia FFI binary layout assumes little-endian native byte order; "
              "see haskell-shim/src/AletheiaFFI.hs:235 for the wire-format note.");

namespace aletheia {

static auto validate_payload(Dlc dlc, std::span<const std::byte> data) -> Result<void> {
    auto expected = dlc_to_bytes(dlc);
    if (data.size() != expected)
        return std::unexpected(
            AletheiaError{ErrorKind::Validation,
                          std::format("payload length {} does not match DLC {} (expected {} bytes)",
                                      data.size(), dlc.value(), expected)});
    return {};
}

// Cancellation error helper. Constructed when a method's pre-FFI guard sees
// stop.stop_requested() and short-circuits before making the FFI call. The
// message includes the method name to mirror Go's
// `fmt.Errorf("method_name: %w", ctx.Err())` wrapping convention.
static auto make_cancellation_error(std::string_view method) -> AletheiaError {
    return AletheiaError{ErrorKind::Cancellation,
                         std::format("{} cancelled by stop_token", method)};
}

AletheiaClient::AletheiaClient(std::unique_ptr<IBackend> backend, Logger logger,
                               std::vector<CheckResult> default_checks)
    : backend_(std::move(backend))
    , state_(backend_->init())
    , logger_(std::move(logger))
    , default_checks_(std::move(default_checks)) {
    if (state_ == nullptr)
        throw AletheiaException(
            AletheiaError{ErrorKind::Ffi, "backend init() returned null state"});
    if (!logger_)
        return;
    // Parity with Go's `rts.cores_mismatch` (ffi.go:336) and Python's
    // `rts.cores_mismatch` (client/_ffi.py:77-82), both of which carry
    // `active_cores` and `requested_cores` integer fields.
    if (auto rts = backend_->rts_mismatch_info(); rts) {
        const auto active = static_cast<std::int64_t>(rts->first);
        const auto requested = static_cast<std::int64_t>(rts->second);
        logger_.warn("rts.cores_mismatch",
                     {{"active_cores", active}, {"requested_cores", requested}});
    }
}

AletheiaClient::~AletheiaClient() {
    if (backend_ != nullptr && state_ != nullptr) {
        try {
            backend_->close(state_);
        } catch (...) {
            // Destructors must not propagate exceptions — doing so during stack
            // unwinding terminates the program. The FFI close() path allocates
            // nothing, but backend implementations (e.g. a mock) may throw; we
            // intentionally swallow those to satisfy the noexcept contract.
            static_cast<void>(std::current_exception());
        }
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
            } catch (...) {
                // noexcept move-assignment must not propagate exceptions. Same
                // rationale as ~AletheiaClient: a throwing backend close is
                // swallowed so the move can complete without std::terminate.
                static_cast<void>(std::current_exception());
            }
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

// Refresh signal name → index cache from a parsed DBC.  Shared between
// parse_dbc (DBC-as-JSON input) and parse_dbc_text (raw DBC text input).
void AletheiaClient::populate_signal_lookup(const DbcDefinition& dbc) {
    signal_index_.clear();
    signal_names_.clear();
    for (const auto& msg : dbc.messages) {
        auto id_value = can_id_value(msg.id);
        auto is_extended = can_id_is_extended(msg.id);
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
}

auto AletheiaClient::parse_dbc(std::stop_token stop, const DbcDefinition& dbc)
    -> Result<ParsedDBC> {
    if (stop.stop_requested()) [[unlikely]]
        return std::unexpected(make_cancellation_error("parse_dbc"));
    auto cmd = detail::serialize_parse_dbc(dbc);
    auto resp = backend_->process(state_, cmd);
    auto result = detail::parse_parsed_dbc(resp);
    if (result.has_value()) {
        populate_signal_lookup(result->dbc);
        if (logger_)
            logger_.info("dbc.parsed",
                         {{"messages", static_cast<std::uint64_t>(result->dbc.messages.size())}});
    }
    return result;
}

auto AletheiaClient::parse_dbc_text(std::stop_token stop, std::string_view text)
    -> Result<ParsedDBC> {
    if (stop.stop_requested()) [[unlikely]]
        return std::unexpected(make_cancellation_error("parse_dbc_text"));
    // Defense-in-depth (cross-binding parity):
    // reject DBC text inputs longer than max_dbc_text_bytes before wrapping
    // them in a JSON command.  The outer max_json_bytes cap in
    // FfiBackend::process covers the wrapped command separately; the
    // additional inner cap matches the Agda kernel's two-layer enforcement
    // in handleParseDBCText.
    if (text.size() > max_dbc_text_bytes) {
        return std::unexpected(
            AletheiaError{ErrorKind::InputBoundExceeded,
                          "input length (bytes) " + std::to_string(text.size()) +
                              " exceeds limit " + std::to_string(max_dbc_text_bytes),
                          ErrorCode::InputBoundExceeded,
                          InputBoundExceededError{
                              .bound_kind = std::string{bound_kind_input_length_bytes},
                              .observed = static_cast<std::uint64_t>(text.size()),
                              .limit = max_dbc_text_bytes,
                          }});
    }
    auto cmd = detail::serialize_parse_dbc_text(text);
    auto resp = backend_->process(state_, cmd);
    auto result = detail::parse_parsed_dbc(resp);
    if (result.has_value()) {
        populate_signal_lookup(result->dbc);
        if (logger_)
            logger_.info("dbc.parsed",
                         {{"messages", static_cast<std::uint64_t>(result->dbc.messages.size())}});
    }
    return result;
}

auto AletheiaClient::validate_dbc(std::stop_token stop, const DbcDefinition& dbc)
    -> Result<ValidationResult> {
    if (stop.stop_requested()) [[unlikely]]
        return std::unexpected(make_cancellation_error("validate_dbc"));
    auto cmd = detail::serialize_validate_dbc(dbc);
    auto resp = backend_->process(state_, cmd);
    return detail::parse_validation(resp);
}

auto AletheiaClient::format_dbc(std::stop_token stop) -> Result<DbcDefinition> {
    if (stop.stop_requested()) [[unlikely]]
        return std::unexpected(make_cancellation_error("format_dbc"));
    auto resp = backend_->format_dbc_binary(state_);
    return detail::parse_dbc_response(resp);
}

auto AletheiaClient::format_dbc_text(std::stop_token stop, const DbcDefinition& dbc)
    -> Result<std::string> {
    if (stop.stop_requested()) [[unlikely]]
        return std::unexpected(make_cancellation_error("format_dbc_text"));
    auto cmd = detail::serialize_format_dbc_text(dbc);
    auto resp = backend_->process(state_, cmd);
    return detail::parse_dbc_text_response(resp);
}

// ---------------------------------------------------------------------------
// Signals
// ---------------------------------------------------------------------------

// Error code → message mapping for binary extraction.  Must match
// `extractionErrorCodeToℕ` + the `resultToString` cases in
// `src/Aletheia/CAN/BatchExtraction.agda` (the constructor-to-code ordering
// in `ExtractionErrorCode` is the wire format).
constexpr std::array extraction_error_messages = {
    std::string_view{"Signal not found in DBC"}, // 0
    std::string_view{"Value out of bounds"},     // 1
    std::string_view{"Extraction failed"},       // 2
};

// Constructs a SignalValue from a wire-extracted (idx, num, den) triple.
// Centralizes the den-positive normalization required for cross-binding
// wire symmetry and keeps `parse_extraction_bin`
// under the clang-tidy readability-function-size threshold.
static auto wire_signal_value(std::uint16_t idx, std::int64_t num, std::int64_t den,
                              const std::vector<std::string>& names) -> Result<SignalValue> {
    auto name =
        idx < names.size() ? SignalName{names[idx]} : SignalName{std::format("signal_{}", idx)};
    if (den == 0)
        return std::unexpected(AletheiaError{
            ErrorKind::Protocol,
            std::format("Zero denominator in extraction value for {}", std::string_view{name})});
    auto rat_or_err = Rational::make(num, den);
    if (!rat_or_err)
        return std::unexpected(
            AletheiaError{ErrorKind::Protocol,
                          std::format("Invalid rational in extraction value for {}: num={}, den={}",
                                      std::string_view{name}, num, den)});
    return SignalValue{.name = std::move(name), .value = PhysicalValue{*rat_or_err}};
}

// Parses the binary extraction layout emitted by `aletheia_extract_signals_bin`.
// Layout and byte-order (native; little-endian on all supported platforms) are
// documented at haskell-shim/src/AletheiaFFI.hs:235 — "Header(3×u16) +
// Values(×18B) + Errors(×3B) + Absent(×2B). Native byte order." Cross-arch
// deployment would require byteswapping on the reader side.
static auto parse_extraction_bin(std::span<const std::byte> buf,
                                 const std::vector<std::string>& names)
    -> Result<ExtractionResult> {
    auto read_u16 = [&](std::size_t off) -> std::uint16_t {
        std::uint16_t v = 0;
        // NOLINTNEXTLINE(cppcoreguidelines-pro-bounds-pointer-arithmetic)
        std::memcpy(&v, buf.data() + off, sizeof(v));
        return v;
    };
    auto read_i64 = [&](std::size_t off) -> std::int64_t {
        std::int64_t v = 0;
        // NOLINTNEXTLINE(cppcoreguidelines-pro-bounds-pointer-arithmetic)
        std::memcpy(&v, buf.data() + off, sizeof(v));
        return v;
    };

    if (buf.size() < 6)
        return std::unexpected(AletheiaError{
            ErrorKind::Protocol,
            std::format("Truncated extraction buffer: {} bytes, need >= 6 for the header",
                        buf.size())});
    const auto nvals = read_u16(0);
    const auto nerrs = read_u16(2);
    const auto nabss = read_u16(4);
    // nvals/nerrs/nabss are u16 (max 65535), so the max expected_size is
    // ~1.5 MB — far below SIZE_MAX on any supported platform.
    const auto expected_size = std::size_t{6} + (std::size_t{nvals} * 18) +
                               (std::size_t{nerrs} * 3) + (std::size_t{nabss} * 2);
    // Exact-size check: too short is truncation, too long is trailing bytes.
    if (buf.size() != expected_size)
        return std::unexpected(AletheiaError{
            ErrorKind::Protocol,
            std::format("Extraction buffer size mismatch: {} bytes, expected exactly {}",
                        buf.size(), expected_size)});
    std::size_t off = 6;

    ExtractionResult result;
    result.values.reserve(nvals);
    for (std::uint16_t i = 0; i < nvals; ++i) {
        // Per-read bounds check — redundant with the upfront expected_size
        // guard above, but keeps the loop locally defensive against future
        // changes to the record layout or header computation.
        if (off + 18 > buf.size())
            return std::unexpected(AletheiaError{
                ErrorKind::Protocol, "Truncated extraction buffer while reading signal values"});
        auto idx = read_u16(off);
        auto num = read_i64(off + 2);
        auto den = read_i64(off + 10);
        off += 18;
        auto sv = wire_signal_value(idx, num, den, names);
        if (!sv)
            return std::unexpected(sv.error());
        result.values.push_back(std::move(*sv));
    }
    result.errors.reserve(nerrs);
    for (std::uint16_t i = 0; i < nerrs; ++i) {
        if (off + 3 > buf.size())
            return std::unexpected(AletheiaError{
                ErrorKind::Protocol, "Truncated extraction buffer while reading signal errors"});
        auto idx = read_u16(off);
        auto code = static_cast<std::uint8_t>(buf[off + 2]);
        off += 3;
        auto name =
            idx < names.size() ? SignalName{names[idx]} : SignalName{std::format("signal_{}", idx)};
        auto msg = code < extraction_error_messages.size()
                       ? std::string{extraction_error_messages[code]}
                       : std::format("Unknown error code {}", code);
        result.errors.push_back({.name = std::move(name), .reason = std::move(msg)});
    }
    result.absent.reserve(nabss);
    for (std::uint16_t i = 0; i < nabss; ++i) {
        if (off + 2 > buf.size())
            return std::unexpected(AletheiaError{
                ErrorKind::Protocol, "Truncated extraction buffer while reading absent signals"});
        auto idx = read_u16(off);
        off += 2;
        auto name =
            idx < names.size() ? SignalName{names[idx]} : SignalName{std::format("signal_{}", idx)};
        result.absent.push_back(std::move(name));
    }
    return result;
}

auto AletheiaClient::extract_signals(std::stop_token stop, CanId id, Dlc dlc,
                                     std::span<const std::byte> data) -> Result<ExtractionResult> {
    if (stop.stop_requested()) [[unlikely]]
        return std::unexpected(make_cancellation_error("extract_signals"));
    if (auto v = validate_payload(dlc, data); !v.has_value())
        return std::unexpected(v.error());

    // Use binary path when signal name cache is populated. Only
    // ErrorKind::BinaryUnsupported (e.g. MockBackend) triggers the JSON
    // fallback — any other error (decode / truncation / real FFI failure)
    // propagates, matching Go's ErrBinaryPathUnsupported contract.
    auto id_value = can_id_value(id);
    auto is_extended = can_id_is_extended(id);
    auto names_it = signal_names_.find(detail::MessageKey{id_value, is_extended});
    if (names_it != signal_names_.end()) {
        auto buf = backend_->extract_signals_bin(state_, id, dlc, data);
        if (buf)
            return parse_extraction_bin(*buf, names_it->second);
        if (buf.error().kind() != ErrorKind::BinaryUnsupported)
            return std::unexpected(buf.error());
        // BinaryUnsupported: fall through to JSON path.
    }

    // Fallback: JSON path.
    auto resp = backend_->extract_signals_binary(state_, id, dlc, data);
    return detail::parse_extraction(std::move(resp));
}

auto AletheiaClient::ResolvedSignals::injection() const -> SignalInjection {
    return {.count = static_cast<std::uint32_t>(indices.size()),
            .indices = indices.data(),
            .numerators = numerators.data(),
            .denominators = denominators.data()};
}

auto AletheiaClient::resolve_signals(CanId id, std::span<const SignalValue> signals)
    -> Result<ResolvedSignals> {
    auto id_value = can_id_value(id);
    auto is_extended = can_id_is_extended(id);

    // Distinguish "this CAN ID has no DBC message" from "this message lacks this
    // signal": without this guard a missing message collapses into the per-signal
    // "signal not found" error below (misleading), and a zero-signal call would
    // silently succeed.  Mirrors Go (resolveSignalIndices) and Python
    // (_resolve_signal_indices), which guard message-existence before iterating.
    if (!signal_names_.contains(detail::MessageKey{id_value, is_extended})) {
        return std::unexpected(AletheiaError{
            ErrorKind::Validation,
            std::format("no DBC message for CAN ID {} (extended={})", id_value, is_extended)});
    }

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
        const auto& r = sv.value.get();
        resolved.numerators.push_back(r.numerator());
        resolved.denominators.push_back(r.denominator());
    }
    return resolved;
}

auto AletheiaClient::build_frame(std::stop_token stop, CanId id, Dlc dlc,
                                 std::span<const SignalValue> signals) -> Result<FramePayload> {
    if (stop.stop_requested()) [[unlikely]]
        return std::unexpected(make_cancellation_error("build_frame"));
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

auto AletheiaClient::update_frame(std::stop_token stop, CanId id, Dlc dlc,
                                  std::span<const std::byte> data,
                                  std::span<const SignalValue> signals) -> Result<FramePayload> {
    if (stop.stop_requested()) [[unlikely]]
        return std::unexpected(make_cancellation_error("update_frame"));
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

auto AletheiaClient::set_properties(std::stop_token stop, std::span<const LtlFormula> properties)
    -> Result<void> {
    if (stop.stop_requested()) [[unlikely]]
        return std::unexpected(make_cancellation_error("set_properties"));
    auto cmd = detail::serialize_set_properties(properties);
    auto resp = backend_->process(state_, cmd);
    auto result = detail::parse_success(resp);
    if (!result.has_value())
        return result;
    // build_diagnostic reaches format_rational_ffi which throws
    // AletheiaException(Ffi) on missing .so; lower to Result<> to honor
    // the documented contract (mirrors add_checks below).
    try {
        diags_.clear();
        diags_.reserve(properties.size());
        for (const auto& f : properties)
            diags_.push_back(build_diagnostic(f));
        cache_.clear();
        if (logger_)
            logger_.info("properties.set",
                         {{"count", static_cast<std::uint64_t>(properties.size())}});
        return result;
    } catch (const AletheiaException& e) {
        return std::unexpected(e.error());
    } catch (const std::exception& e) {
        return std::unexpected(AletheiaError{ErrorKind::Ffi, e.what()});
    }
}

auto AletheiaClient::add_checks(std::stop_token stop, std::vector<CheckResult> checks)
    -> Result<void> {
    if (stop.stop_requested()) [[unlikely]]
        return std::unexpected(make_cancellation_error("add_checks"));
    try {
        std::vector<LtlFormula> formulas;
        formulas.reserve(default_checks_.size() + checks.size());
        auto push_check = [&](const CheckResult& c, std::string_view origin) -> Result<void> {
            const auto& f = c.formula();
            if (!f)
                return std::unexpected(AletheiaError{
                    ErrorKind::Validation, std::string(origin) + " check has no formula"});
            formulas.push_back(ltl::clone(*f));
            return {};
        };
        for (const auto& dc : default_checks_) {
            auto r = push_check(dc, "default");
            if (!r)
                return r;
        }
        for (const auto& check : checks) {
            auto r = push_check(check, "user");
            if (!r)
                return r;
        }
        return set_properties(stop, formulas);
    } catch (const AletheiaException& e) {
        return std::unexpected(e.error());
    } catch (const std::exception& e) {
        return std::unexpected(AletheiaError{ErrorKind::Validation, e.what()});
    }
}

auto AletheiaClient::start_stream(std::stop_token stop) -> Result<void> {
    if (stop.stop_requested()) [[unlikely]]
        return std::unexpected(make_cancellation_error("start_stream"));
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

auto AletheiaClient::send_frame(std::stop_token stop, Timestamp ts, CanId id, Dlc dlc,
                                std::span<const std::byte> data, std::optional<bool> brs,
                                std::optional<bool> esi) -> Result<FrameResponse> {
    if (stop.stop_requested()) [[unlikely]]
        return std::unexpected(make_cancellation_error("send_frame"));
    if (ts.count() < 0)
        return std::unexpected(
            AletheiaError{ErrorKind::Validation, "timestamp must be non-negative"});
    if (auto v = validate_payload(dlc, data); !v.has_value())
        return std::unexpected(v.error());
    auto resp = backend_->send_frame_binary(state_, ts, id, dlc, data, brs, esi);
    auto result = detail::parse_frame_response(resp);
    if (result.has_value()) {
        auto id_value = can_id_value(id);
        auto is_extended = can_id_is_extended(id);
        // Track last frame per CAN ID for end-of-stream enrichment (skip when no diagnostics).
        // Find-then-assign reuses the existing FramePayload's heap buffer
        // on subsequent frames for the same key — `assign` keeps the vector's
        // capacity intact when the new size fits, avoiding the temporary
        // `FramePayload(data.begin(), data.end())` allocation that
        // `insert_or_assign` would force per call.  First frame for a key
        // still allocates via `emplace`; this is the common cold path on a
        // bounded number of unique CAN IDs.
        if (!diags_.empty()) {
            auto key = detail::MessageKey{id_value, is_extended};
            if (auto it = last_frames_.find(key); it != last_frames_.end()) {
                it->second.id = id;
                it->second.dlc = dlc;
                it->second.data.assign(data.begin(), data.end());
            } else {
                last_frames_.emplace(
                    key, LastFrame{
                             .id = id, .dlc = dlc, .data = FramePayload(data.begin(), data.end())});
            }
        }
        // PropertyBatch may carry mid-stream
        // Satisfactions + a terminal Violation; enrich each fails entry
        // and emit the standard frame.processed log event.  Extracted
        // into a helper to keep send_frame under clang-tidy's
        // cognitive-complexity threshold (25).
        finalize_frame_response(*result, ts, id, dlc, data, id_value, is_extended);
    }
    return result;
}

auto AletheiaClient::send_frames(std::stop_token stop, std::span<const Frame> frames)
    -> BatchResult {
    BatchResult batch;
    batch.responses.reserve(frames.size());
    for (std::size_t i = 0; i < frames.size(); ++i) {
        // Per-frame check between FFI calls — the cancellation boundary for
        // batch ops. The most recent FFI call (if one was in flight when stop
        // fired) ran to completion and its response is in `responses`.
        if (stop.stop_requested()) [[unlikely]] {
            batch.error = make_cancellation_error("send_frames");
            return batch;
        }
        auto r = send_frame(stop, frames[i]);
        if (!r.has_value()) {
            auto& e = r.error();
            // Cancellation propagates as-is so callers see ErrorKind::Cancellation
            // rather than a misleading "frame N: ..." wrap.
            if (e.kind() == ErrorKind::Cancellation) {
                batch.error = e;
            } else {
                // Forward `bound_info_` so a
                // mid-batch `InputBoundExceededError` payload survives the
                // per-frame context wrap.  Without this the 3-arg ctor
                // defaulted `bound_info` to `std::nullopt`, dropping the
                // structured `bound_kind/observed/limit` triple that the
                // Python `InputBoundExceededError` and Go `*InputBoundExceededError`
                // preserve across error paths.
                batch.error = AletheiaError{e.kind(), std::format("frame {}: {}", i, e.message()),
                                            e.code(), e.bound_info()};
            }
            return batch;
        }
        batch.responses.push_back(std::move(*r));
    }
    return batch;
}

auto AletheiaClient::send_error(std::stop_token stop, Timestamp ts) -> Result<void> {
    if (stop.stop_requested()) [[unlikely]]
        return std::unexpected(make_cancellation_error("send_error"));
    if (ts.count() < 0)
        return std::unexpected(
            AletheiaError{ErrorKind::Validation, "timestamp must be non-negative"});
    auto resp = backend_->send_error_binary(state_, ts);
    auto r = detail::parse_event_ack(resp);
    if (r.has_value() && logger_.enabled(LogLevel::Debug)) {
        logger_.debug("error_event.sent", {{"ts", static_cast<std::int64_t>(ts.count())},
                                           {"response", std::string_view{"ack"}}});
    }
    return r;
}

auto AletheiaClient::send_remote(std::stop_token stop, Timestamp ts, CanId id) -> Result<void> {
    if (stop.stop_requested()) [[unlikely]]
        return std::unexpected(make_cancellation_error("send_remote"));
    if (ts.count() < 0)
        return std::unexpected(
            AletheiaError{ErrorKind::Validation, "timestamp must be non-negative"});
    auto resp = backend_->send_remote_binary(state_, ts, id);
    auto r = detail::parse_event_ack(resp);
    if (r.has_value() && logger_.enabled(LogLevel::Debug)) {
        logger_.debug(
            "remote_event.sent",
            {{"ts", static_cast<std::int64_t>(ts.count())},
             {"canId", static_cast<std::uint64_t>(std::visit(
                           [](const auto& v) -> std::uint32_t { return v.value(); }, id))},
             {"extended", can_id_is_extended(id)},
             {"response", std::string_view{"ack"}}});
    }
    return r;
}

auto AletheiaClient::end_stream(std::stop_token stop) -> Result<StreamResult> {
    if (stop.stop_requested()) [[unlikely]]
        return std::unexpected(make_cancellation_error("end_stream"));
    auto resp = backend_->end_stream_binary(state_);
    auto result = detail::parse_stream_result(resp);
    if (result.has_value()) {
        if (!diags_.empty())
            enrich_end_stream_results(*result);
        if (logger_)
            log_end_stream_summary(*result);
        last_frames_.clear();
    }
    return result;
}

void AletheiaClient::log_end_stream_summary(const StreamResult& result) {
    std::uint64_t num_fails = 0;
    std::uint64_t num_unresolved = 0;
    for (const auto& pr : result.results) {
        if (pr.verdict == Verdict::Fails)
            ++num_fails;
        else if (pr.verdict == Verdict::Unresolved)
            ++num_unresolved;
    }
    for (const auto& w : result.warnings) {
        if (w.kind == "uncached_atom") {
            logger_.warn("endstream.uncached_atom",
                         {{"property_index", static_cast<std::uint64_t>(w.property_index.get())},
                          {"detail", std::string_view{w.detail}}});
        }
    }
    logger_.info("stream.ended",
                 {{"numResults", static_cast<std::uint64_t>(result.results.size())},
                  {"numFails", num_fails},
                  {"numUnresolved", num_unresolved},
                  {"numWarnings", static_cast<std::uint64_t>(result.warnings.size())}});
}

// ---------------------------------------------------------------------------
// Enrichment internals
// ---------------------------------------------------------------------------

static auto collect_matching_signals(const PropertyDiagnostic& diag,
                                     const ExtractionResult& extraction)
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

static auto format_enriched_reason(const PropertyDiagnostic& diag,
                                   const std::map<SignalName, PhysicalValue>& values,
                                   std::string_view core_reason) -> std::string {
    std::string reason;
    bool rendered = false;
    if (!values.empty()) {
        // Best-effort on the eval path: rendering the observed values needs the
        // runtime, which is up here (the frame was processed through it) — so this
        // is unreachable — but never sink an already-processed frame if the kernel
        // renderer throws. Degrade to the formula description (no value rendered,
        // no local fallback). set_properties, by contrast, propagates the throw.
        try {
            std::string parts;
            bool first = true;
            for (const auto& sig : diag.signals) {
                if (auto it = values.find(sig); it != values.end()) {
                    if (!first)
                        parts += ", ";
                    // Render the observed value via the kernel formatℚ (same renderer
                    // as the predicate threshold) — exact, not lossy %g/to_double(),
                    // and byte-identical to the other bindings.
                    parts +=
                        std::format("{} = {}", std::string_view{sig},
                                    detail::format_rational_ffi(it->second.get().numerator(),
                                                                it->second.get().denominator()));
                    first = false;
                }
            }
            if (!first) {
                reason = parts + " (formula: " + diag.formula_desc + ")";
                rendered = true;
            }
        } catch (const AletheiaException&) {
            rendered = false;
        }
    }
    if (!rendered)
        reason = "violated: " + diag.formula_desc;
    if (!core_reason.empty())
        reason += " [core: " + std::string{core_reason} + "]";
    return reason;
}

void AletheiaClient::finalize_frame_response(FrameResponse& fr, Timestamp ts, CanId id, Dlc dlc,
                                             std::span<const std::byte> data,
                                             std::uint32_t id_value, bool is_extended) {
    auto* batch = std::get_if<PropertyBatch>(&fr);
    if (batch != nullptr && !diags_.empty()) {
        bool has_fail = false;
        for (auto& entry : batch->results) {
            if (entry.verdict == Verdict::Fails) {
                enrich_violation(entry, id, dlc, data, id_value, is_extended);
                has_fail = true;
            }
        }
        if (logger_.enabled(LogLevel::Debug))
            logger_.debug(
                "frame.processed",
                {{"ts", static_cast<std::int64_t>(ts.count())},
                 {"canId", static_cast<std::uint64_t>(id_value)},
                 {"extended", is_extended},
                 {"response", std::string_view{has_fail ? "violation" : "satisfaction"}}});
        return;
    }
    if (logger_.enabled(LogLevel::Debug))
        logger_.debug("frame.processed", {{"ts", static_cast<std::int64_t>(ts.count())},
                                          {"canId", static_cast<std::uint64_t>(id_value)},
                                          {"extended", is_extended},
                                          {"response", std::string_view{"ack"}}});
}

void AletheiaClient::enrich_violation(PropertyResult& pr, CanId id, Dlc dlc,
                                      std::span<const std::byte> data, std::uint32_t id_value,
                                      bool is_extended) {
    auto& v = pr;
    auto idx = v.property_index.get();
    if (idx >= diags_.size()) {
        // Property index out of range — protocol mismatch; skip enrichment.
        if (logger_)
            logger_.warn("enrichment.property_index_oob",
                         {{"index", static_cast<std::int64_t>(idx)},
                          {"count", static_cast<std::uint64_t>(diags_.size())}});
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

void AletheiaClient::enrich_end_stream_results(StreamResult& result) {
    auto todo = collect_enrichable_results(result);
    if (todo.empty())
        return;

    // Union of the signal names any collected diagnostic wants. When the
    // union is empty, skip the frame extraction loop entirely (zero FFI
    // extraction calls, no extraction_failed warnings) — but still attach
    // an enrichment to every collected result via the empty-values fallback.
    std::set<SignalName> wanted;
    for (const auto& [pr, diag] : todo)
        wanted.insert(diag->signals.begin(), diag->signals.end());
    std::map<SignalName, PhysicalValue> merged;
    if (!wanted.empty())
        merged = merge_last_known_values(std::move(wanted));

    // Distribute: each result's values are the merged map filtered to its
    // own diagnostic's signals; the enrichment is always attached (empty
    // values degrade to the "violated: <formula>" fallback reason).
    for (auto& [pr, diag] : todo) {
        std::map<SignalName, PhysicalValue> values;
        for (const auto& sig : diag->signals) {
            if (auto it = merged.find(sig); it != merged.end())
                values.emplace(sig, it->second);
        }
        auto reason = format_enriched_reason(*diag, values, pr->reason);
        pr->enrichment = ViolationEnrichment{
            .signals = std::move(values),
            .formula_desc = diag->formula_desc,
            .enriched_reason = std::move(reason),
            .core_reason = pr->reason,
        };
    }
}

auto AletheiaClient::collect_enrichable_results(StreamResult& result)
    -> std::vector<std::pair<PropertyResult*, const PropertyDiagnostic*>> {
    std::vector<std::pair<PropertyResult*, const PropertyDiagnostic*>> todo;
    for (auto& pr : result.results) {
        if (pr.verdict != Verdict::Fails && pr.verdict != Verdict::Unresolved)
            continue;
        auto idx = pr.property_index.get();
        if (idx >= diags_.size()) {
            // Property index out of range — protocol mismatch; skip enrichment.
            if (logger_)
                logger_.warn("enrichment.property_index_oob",
                             {{"index", static_cast<std::int64_t>(idx)},
                              {"count", static_cast<std::uint64_t>(diags_.size())}});
            continue;
        }
        todo.emplace_back(&pr, &diags_[idx]);
    }
    return todo;
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
        if (logger_.enabled(LogLevel::Debug))
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
                logger_.warn("cache.full", {{"size", static_cast<std::uint64_t>(cache_.size())}});
            // Over capacity — use result directly without caching
            return collect_matching_signals(diag, *extraction);
        }
    } else if (logger_.enabled(LogLevel::Debug)) {
        logger_.debug("cache.hit", {{"canId", static_cast<std::uint64_t>(id_value)},
                                    {"dlc", static_cast<std::uint64_t>(dlc.value())}});
    }

    return collect_matching_signals(diag, cache_it->second);
}

auto AletheiaClient::merge_last_known_values(std::set<SignalName> remaining)
    -> std::map<SignalName, PhysicalValue> {
    // One full-frame extraction per tracked frame, in ascending
    // (CAN id value, extended) order — std::map's key order is the sorted
    // contract. Every extracted signal merges first-frame-wins (emplace
    // never overwrites); a failed extraction warns once per frame per
    // end_stream. Stops early once every remaining wanted name is merged.
    std::map<SignalName, PhysicalValue> merged;
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
            if (merged.emplace(sv.name, sv.value).second)
                remaining.erase(sv.name);
        }
        if (remaining.empty())
            break;
    }
    return merged;
}

auto AletheiaClient::extract_signals_internal(CanId id, Dlc dlc, std::span<const std::byte> data,
                                              std::uint32_t id_value, bool is_extended)
    -> std::optional<ExtractionResult> {
    // Use binary path when signal name cache is populated. Mirrors the
    // ErrorKind::BinaryUnsupported fallback contract in extract_signals:
    // only that kind triggers the JSON fallback; any other error is a real
    // failure (decode / truncation / genuine FFI error) logged + surfaced
    // as std::nullopt.
    auto names_it = signal_names_.find(detail::MessageKey{id_value, is_extended});
    if (names_it != signal_names_.end()) {
        auto buf = backend_->extract_signals_bin(state_, id, dlc, data);
        if (buf) {
            auto bin_result = parse_extraction_bin(*buf, names_it->second);
            if (!bin_result) {
                if (logger_)
                    logger_.warn("extraction.parse_failed",
                                 {{"canId", static_cast<std::uint64_t>(id_value)},
                                  {"error", bin_result.error().message()}});
                return std::nullopt;
            }
            return std::move(*bin_result);
        }
        if (buf.error().kind() != ErrorKind::BinaryUnsupported) {
            if (logger_)
                logger_.warn("extraction.process_failed",
                             {{"canId", static_cast<std::uint64_t>(id_value)},
                              {"error", buf.error().message()}});
            return std::nullopt;
        }
        // BinaryUnsupported: fall through to JSON path.
    }

    // Fallback: JSON path.
    //
    // Matches the binary path's "log + return nullopt for any kind != BinaryUnsupported"
    // convention at lines 850-855 above.  AletheiaException from the FFI backend is
    // caught via its std::runtime_error base; the log warning carries the message but no
    // kind field, to preserve cross-binding parity with Python / Go's
    // `extraction.process_failed` event signature.
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
