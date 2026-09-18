// SPDX-FileCopyrightText: 2025 Nicolas Pelletier
// SPDX-License-Identifier: BSD-2-Clause
// JSON parsing: Agda core response strings → C++ types.
#include "detail/json.hpp"

#include <aletheia/limits.hpp>

#include <nlohmann/json.hpp>

#include <array>
#include <cstddef>
#include <cstdint>
#include <exception>
#include <expected>
#include <limits>
#include <optional>
#include <stdexcept>
#include <string>
#include <string_view>
#include <type_traits>
#include <utility>
#include <vector>

using Json = nlohmann::json;

namespace aletheia {

namespace {

// String → ErrorCode lookup table. Grouped by error family for readability;
// the order within each group mirrors the Agda error ADTs.
using ErrorCodeEntry = std::pair<std::string_view, ErrorCode>;
constexpr auto error_code_table = std::to_array<ErrorCodeEntry>({
    // Parse errors
    {"parse_missing_field", ErrorCode::ParseMissingField},
    {"parse_invalid_byte_order", ErrorCode::ParseInvalidByteOrder},
    {"parse_invalid_presence", ErrorCode::ParseInvalidPresence},
    {"parse_missing_signed", ErrorCode::ParseMissingSigned},
    {"parse_invalid_signed", ErrorCode::ParseInvalidSigned},
    {"parse_not_an_object", ErrorCode::ParseNotAnObject},
    {"parse_ext_can_id_out_of_range", ErrorCode::ParseExtCanIdOutOfRange},
    {"parse_std_can_id_out_of_range", ErrorCode::ParseStdCanIdOutOfRange},
    {"parse_default_can_id_out_of_range", ErrorCode::ParseDefaultCanIdOutOfRange},
    {"parse_invalid_dlc_bytes", ErrorCode::ParseInvalidDlcBytes},
    {"parse_root_not_object", ErrorCode::ParseRootNotObject},
    {"parse_missing_signal_name", ErrorCode::ParseMissingSignalName},
    {"parse_signal_bit_length_zero", ErrorCode::ParseSignalBitLengthZero},
    {"parse_signal_start_bit_exceeds_frame", ErrorCode::ParseSignalStartBitExceedsFrame},
    {"parse_signal_bit_length_exceeds_frame", ErrorCode::ParseSignalBitLengthExceedsFrame},
    {"parse_signal_big_endian_overflow", ErrorCode::ParseSignalBigEndianOverflow},
    {"parse_invalid_kind", ErrorCode::ParseInvalidKind},
    {"parse_non_terminating_rational", ErrorCode::ParseNonTerminatingRational},
    {"parse_invalid_identifier", ErrorCode::ParseInvalidIdentifier},
    {"parse_non_integer_multiplex_value", ErrorCode::ParseNonIntegerMultiplexValue},
    {"parse_non_natural_field", ErrorCode::ParseNonNaturalField},
    // DBC text parse errors
    {"dbc_text_parse_failure", ErrorCode::DBCTextParseFailure},
    {"dbc_text_trailing_input", ErrorCode::DBCTextTrailingInput},
    {"dbc_text_attribute_refinement_failed", ErrorCode::DBCTextAttributeRefinementFailed},
    // Frame errors
    {"frame_signal_not_found", ErrorCode::FrameSignalNotFound},
    {"frame_signal_index_oob", ErrorCode::FrameSignalIndexOob},
    {"frame_injection_failed", ErrorCode::FrameInjectionFailed},
    {"frame_signals_overlap", ErrorCode::FrameSignalsOverlap},
    {"frame_can_id_not_found", ErrorCode::FrameCanIdNotFound},
    {"frame_can_id_mismatch", ErrorCode::FrameCanIdMismatch},
    {"frame_signal_value_out_of_bounds", ErrorCode::FrameSignalValueOutOfBounds},
    // Top-level adversarial-input bound
    {"input_bound_exceeded", ErrorCode::InputBoundExceeded},
    // Route errors
    {"route_missing_field", ErrorCode::RouteMissingField},
    {"route_missing_array", ErrorCode::RouteMissingArray},
    {"route_unknown_command", ErrorCode::RouteUnknownCommand},
    {"route_missing_command_field", ErrorCode::RouteMissingCommandField},
    {"route_dlc_exceeds_max", ErrorCode::RouteDlcExceedsMax},
    {"route_byte_array_parse_failed", ErrorCode::RouteByteArrayParseFailed},
    {"route_byte_count_mismatch", ErrorCode::RouteByteCountMismatch},
    {"route_missing_dbc_field", ErrorCode::RouteMissingDbcField},
    {"route_missing_props_field", ErrorCode::RouteMissingPropsField},
    // Handler errors
    {"handler_no_dbc", ErrorCode::HandlerNoDbc},
    {"handler_already_streaming", ErrorCode::HandlerAlreadyStreaming},
    {"handler_not_streaming", ErrorCode::HandlerNotStreaming},
    {"handler_stream_not_started", ErrorCode::HandlerStreamNotStarted},
    {"handler_stream_active", ErrorCode::HandlerStreamActive},
    {"handler_property_parse_failed", ErrorCode::HandlerPropertyParseFailed},
    {"handler_invalid_dlc_code", ErrorCode::HandlerInvalidDlcCode},
    {"handler_validation_failed", ErrorCode::HandlerValidationFailed},
    {"handler_text_roundtrip_failed", ErrorCode::HandlerTextRoundtripFailed},
    {"handler_non_monotonic_timestamp", ErrorCode::HandlerNonMonotonicTimestamp},
    // Dispatch errors
    {"dispatch_missing_type_field", ErrorCode::DispatchMissingTypeField},
    {"dispatch_unknown_message_type", ErrorCode::DispatchUnknownMessageType},
    {"dispatch_invalid_json", ErrorCode::DispatchInvalidJson},
    {"dispatch_request_not_object", ErrorCode::DispatchRequestNotObject},
    // Extraction errors
    {"extraction_mux_value_mismatch", ErrorCode::ExtractionMuxValueMismatch},
    {"extraction_mux_signal_not_found", ErrorCode::ExtractionMuxSignalNotFound},
    {"extraction_mux_chain_cycle", ErrorCode::ExtractionMuxChainCycle},
    {"extraction_mux_extraction_failed", ErrorCode::ExtractionMuxExtractionFailed},
    {"extraction_bit_extraction_failed", ErrorCode::ExtractionBitExtractionFailed},
    {"extraction_value_exceeds_wire_range", ErrorCode::ExtractionValueExceedsWireRange},
});

} // namespace

// The value of a table entry, or nullopt when the table has no such entry.
// Every string-to-enum table in this file is an array scanned linearly, which
// is fine on these cold paths.
template<typename Table>
static auto lookup(const Table& table, std::string_view wire)
    -> std::optional<typename Table::value_type::second_type> {
    for (auto const& [name, value] : table)
        if (name == wire)
            return value;
    return std::nullopt;
}

auto error_code_from_string(std::string_view s) -> ErrorCode {
    return lookup(error_code_table, s).value_or(ErrorCode::Unknown);
}

} // namespace aletheia

namespace aletheia::detail {

// ---------------------------------------------------------------------------
// Helpers
// ---------------------------------------------------------------------------

static auto make_error(ErrorKind kind, std::string msg, ErrorCode code = ErrorCode::Unknown)
    -> AletheiaError {
    return {kind, std::move(msg), code};
}

// Reject a JSON float in an integer-only wire position.  nlohmann silently
// `static_cast`s a JSON float to an integer type on `get<intT>()` (e.g.
// 5.9 → 5), corrupting the value *before* any range check runs.  The FFI wire
// and DBC integer-position fields are integer-only by construction — the Agda
// core never emits a float there — so a non-integer number is a wire-format
// violation and is rejected here rather than silently truncated.  Exact
// rationals travel as `{numerator, denominator}` objects, never as floats.
//
// `require_int` accepts negatives (signed positions); `require_uint` rejects
// negatives as well as floats (`is_number_unsigned` is false for both).  Both
// preserve the caller's existing range check, which still runs on the returned
// integer.
//
// Both also refuse a value the position cannot hold.  The JSON library keeps
// a positive literal above the signed maximum as an unsigned one, and the
// narrowing conversion wraps it: without this check an index one past the
// signed 64-bit maximum reads as the most negative one and the caller's sign
// test calls it negative, a CAN id of 2^32 reads as a valid zero, a frame
// byte of 256 reads as zero.  The refusal names the position's own range, as
// the kernel names the Int64 wire range it refuses at its own entry.
template<typename T>
static auto out_of_range(const Json& j, std::string_view context) -> std::runtime_error {
    return std::runtime_error(std::string{context} + " is out of range (" +
                              std::to_string(std::numeric_limits<T>::min()) + " to " +
                              std::to_string(std::numeric_limits<T>::max()) +
                              "), got: " + j.dump());
}

template<typename T>
static auto require_int(const Json& j, std::string_view context) -> T {
    if (!j.is_number_integer())
        throw std::runtime_error(std::string{context} + " must be an integer, got: " + j.dump());
    // A signed value always fits a 64-bit target, so that branch is a check
    // only for narrower targets.
    bool fits = true;
    if (j.is_number_unsigned())
        fits = std::in_range<T>(j.get<std::uint64_t>());
    else if constexpr (!std::is_same_v<T, std::int64_t>)
        fits = std::in_range<T>(j.get<std::int64_t>());
    if (!fits)
        throw out_of_range<T>(j, context);
    return j.get<T>();
}

template<typename T>
static auto require_uint(const Json& j, std::string_view context) -> T {
    if (!j.is_number_unsigned())
        throw std::runtime_error(std::string{context} +
                                 " must be a non-negative integer, got: " + j.dump());
    auto const wide = j.get<std::uint64_t>();
    // A 64-bit unsigned target holds every value the reader can produce, so
    // the range check exists only for the narrower ones.
    if constexpr (std::numeric_limits<T>::max() < std::numeric_limits<std::uint64_t>::max()) {
        if (!std::in_range<T>(wide))
            throw out_of_range<T>(j, context);
    }
    return static_cast<T>(wide);
}

// Parse JSON with the `max_nesting_depth` bound enforced via nlohmann's
// SAX-style parse callback.  Defense-in-depth against malformed-but-bound-
// passing responses (the FFI-entry size cap fires first for oversize inputs;
// a 1 MiB response with 10⁵ nesting still depth-bombs the recursive-descent
// parser via stack overflow without this guard).  See AGENTS.md universal
// rule "Adversarial-input bounds at parser surfaces".
//
// Throws `std::runtime_error` (not typed `InputBoundExceeded`) by design:
// `InputBoundExceeded` carries the kernel-side `bound_kind / observed / limit`
// triple, whose `bound_kind` is one of the kernel's own `BoundKind`
// constructors (see `src/Aletheia/Limits.agda`).
// JSON nesting depth is a client-side guard against malformed *responses*
// from the kernel — not an inbound kernel input bound — so it doesn't fit
// any `BoundKind` and the typed shape would be misleading.  The existing
// `catch (const std::exception&)` block at every parse_* callsite converts
// the `runtime_error` to a `Result<>` error via `make_error(ErrorKind::Protocol,
// ...)`, which is the right semantic class (malformed/corrupted server reply).
static auto parse_bounded(std::string_view input) -> Json {
    auto const callback = [](int depth, Json::parse_event_t /*event*/, Json& /*parsed*/) -> bool {
        if (std::cmp_greater(depth, max_nesting_depth)) {
            throw std::runtime_error("JSON nesting depth " + std::to_string(depth) +
                                     " exceeds limit " + std::to_string(max_nesting_depth));
        }
        return true;
    };
    return Json::parse(input, callback);
}

// Defined with the issue-code table further down; needed by the
// handler_validation_failed lift below.
static auto parse_issue_entry(const Json& issue) -> Result<ValidationIssue>;

// Lift the structured issues array from a handler_validation_failed envelope
// (parseDBC / parseDBCText rejects carry the same {severity, code, detail}
// elements as a validation response).  `has_errors` and every `issues`
// element must be present and well-typed for the lift to populate; a
// malformed payload degrades to nullopt rather than a Protocol error, so the
// AletheiaError still carries kind/code/message — the same rule as the
// bound_info lift in make_json_error.
static auto lift_validation_issues(const Json& j) -> std::optional<std::vector<ValidationIssue>> {
    if (!j.contains("has_errors") || !j.at("has_errors").is_boolean() || !j.contains("issues") ||
        !j.at("issues").is_array())
        return std::nullopt;
    std::vector<ValidationIssue> issues;
    try {
        for (auto const& issue : j.at("issues")) {
            auto entry = parse_issue_entry(issue);
            if (!entry)
                return std::nullopt;
            issues.push_back(std::move(*entry));
        }
    } catch (const std::exception&) {
        // A non-object element or an ill-typed field throws from nlohmann's
        // value(); degrade identically to a failed entry parse.
        return std::nullopt;
    }
    return issues;
}

/// Extract error from a JSON response with status=="error", parsing the code field.
///
/// Both ``code`` and ``message`` must be non-null strings — a missing or
/// non-string value surfaces as a ``Protocol`` error rather than being
/// papered over with a default, which would turn a malformed response into a
/// plausible-looking one. Matches Python's ``build_error_response``.
static auto make_json_error(ErrorKind kind, const Json& j) -> AletheiaError {
    if (!j.contains("code") || !j.at("code").is_string())
        return make_error(ErrorKind::Protocol, "Error response missing or non-string 'code' field");
    if (!j.contains("message") || !j.at("message").is_string())
        return make_error(ErrorKind::Protocol,
                          "Error response missing or non-string 'message' field");
    auto const code = error_code_from_string(j.at("code").get<std::string>());
    // The bound code carries its own kind whatever the caller guessed from the
    // response section, so the typed bound-info shape is uniform across the
    // JSON, DBC-text and binary parser surfaces, as in the Python and Go
    // bindings' typed input-bound errors.
    auto effective_kind =
        code == ErrorCode::InputBoundExceeded ? ErrorKind::InputBoundExceeded : kind;
    // A round-trip refusal gets its own kind regardless of the caller's default,
    // so a caller discriminates it from a structural validation failure by kind().
    if (code == ErrorCode::HandlerTextRoundtripFailed)
        effective_kind = ErrorKind::TextRoundtrip;
    // Lift the structured `bound_kind / observed / limit` triple into the
    // AletheiaError when the response carries it.  All three must be
    // present and well-typed for `bound_info` to be populated; partial
    // fields are treated as nullopt rather than as a Protocol error, so
    // older Agda responses (or future cores that drop the fields) degrade
    // gracefully (the AletheiaError still carries kind/code/message).
    std::optional<InputBoundExceededError> bound_info;
    if (effective_kind == ErrorKind::InputBoundExceeded && j.contains("bound_kind") &&
        j.at("bound_kind").is_string() && j.contains("observed") &&
        j.at("observed").is_number_unsigned() && j.contains("limit") &&
        j.at("limit").is_number_unsigned()) {
        bound_info = InputBoundExceededError{
            .bound_kind = j.at("bound_kind").get<std::string>(),
            .observed = j.at("observed").get<std::uint64_t>(),
            .limit = j.at("limit").get<std::uint64_t>(),
        };
    }
    std::optional<std::vector<ValidationIssue>> issues;
    if (code == ErrorCode::HandlerValidationFailed || code == ErrorCode::HandlerTextRoundtripFailed)
        issues = lift_validation_issues(j);
    return AletheiaError{effective_kind, j.at("message").get<std::string>(), code,
                         std::move(bound_info), std::move(issues)};
}

// Decode an optional array field: absent means empty, present means every
// element goes through `parse_element`.  A required array keeps its own
// `j.at(...)` loop so a missing one still throws.
template<typename Parse>
static auto parse_optional_array(const Json& j, const char* key, Parse parse_element)
    -> std::vector<std::invoke_result_t<Parse, const Json&>> {
    std::vector<std::invoke_result_t<Parse, const Json&>> out;
    if (!j.contains(key))
        return out;
    auto const& arr = j.at(key);
    for (auto const& elem : arr)
        out.push_back(parse_element(elem));
    return out;
}

// Decode a JSON {numerator, denominator} object into a (num, den) pair,
// validating den > 0.  Caller is responsible for first verifying
// `j.is_object() && j.contains("numerator") && j.contains("denominator")`.
static auto parse_rational_dict(const Json& j) -> std::pair<std::int64_t, std::int64_t> {
    auto const num = require_int<std::int64_t>(j.at("numerator"), "rational numerator");
    auto const den = require_int<std::int64_t>(j.at("denominator"), "rational denominator");
    // The kernel emits rationals with a positive denominator (the ℕ⁺ invariant),
    // so a non-positive denominator is a wire-format violation — rejected here
    // rather than silently sign-normalized.  Mirrors Python
    // (extract_rational_from_dict), Go (parseRational), and Rust (Rational::new),
    // which all reject den <= 0 at the wire instead of rewriting it, so a
    // malformed payload surfaces rather than hiding.
    if (den <= 0)
        throw std::runtime_error("Non-positive denominator in rational: " + j.dump());
    return {num, den};
}

// Decode the `aletheia_parse_decimal` wire envelope into an exact Rational
// (declared in detail/json.hpp). Defined in this TU so it reuses the static
// `parse_rational_dict` above directly — no cross-TU lift. The kernel emits a
// bare `{"numerator","denominator"}` on success or a `{"status":"error",...}`
// envelope on failure; branch on the status BEFORE decoding so the precise
// `decimal_parse_failed` / `decimal_overflow` message survives (otherwise the
// wire decoder reports an opaque "missing numerator" and masks the reason).
// Throws AletheiaException — NOT a bare AletheiaError — because AletheiaError is
// not a std::exception, and the YAML / Excel loaders catch `std::runtime_error`
// (which AletheiaException subclasses); a bare throw would escape them entirely.
auto decode_decimal_response(std::string_view raw) -> Rational {
    Json j;
    try {
        j = parse_bounded(raw);
    } catch (const std::exception& e) {
        // Unreachable for the kernel's own output; an unparsable envelope is an
        // ABI/kernel malfunction, so report it as Protocol (mirrors Rust).
        throw AletheiaException(
            make_error(ErrorKind::Protocol,
                       std::string{"aletheia_parse_decimal: malformed response: "} + e.what()));
    }
    if (j.contains("status") && j.at("status") == "error")
        throw AletheiaException(make_error(
            ErrorKind::Validation, j.value("message", std::string{"invalid decimal literal"})));
    auto [num, den] = parse_rational_dict(j);
    return Rational{num, den};
}

// Agda emits an exact rational as an integer or as
// {"numerator": n, "denominator": d}.  A bare float is rejected: the wire
// carries exact rationals only, so a float is a wire-format violation rather
// than a value to approximate, which is how the Go, Rust and Python decoders
// treat it too.  Throws on any other shape; callers catch at the public API
// boundary.
static auto parse_rational(const Json& j) -> Rational {
    if (j.is_number_integer())
        return Rational{require_int<std::int64_t>(j, "rational integer"), std::int64_t{1}};
    if (j.is_object() && j.contains("numerator") && j.contains("denominator")) {
        auto [num, den] = parse_rational_dict(j);
        return Rational{num, den};
    }
    throw std::runtime_error("Expected integer or {numerator, denominator}, got: " + j.dump());
}

// String → IssueCode lookup table.  Same shape as `error_code_table` at the
// top of this file; linear scan is fine on the cold validation path.
using IssueCodeEntry = std::pair<std::string_view, IssueCode>;
constexpr auto issue_code_table = std::to_array<IssueCodeEntry>({
    {"duplicate_message_id", IssueCode::DuplicateMessageId},
    {"duplicate_message_name", IssueCode::DuplicateMessageName},
    {"duplicate_signal_name", IssueCode::DuplicateSignalName},
    {"factor_zero", IssueCode::FactorZero},
    {"multiplexor_not_found", IssueCode::MultiplexorNotFound},
    {"multiplexor_cycle", IssueCode::MultiplexorCycle},
    {"global_name_collision", IssueCode::GlobalNameCollision},
    {"min_exceeds_max", IssueCode::MinExceedsMax},
    {"signal_exceeds_dlc", IssueCode::SignalExceedsDlc},
    {"signal_overlap", IssueCode::SignalOverlap},
    {"bit_length_zero", IssueCode::BitLengthZero},
    {"offset_scale_range", IssueCode::OffsetScaleRange},
    {"empty_message", IssueCode::EmptyMessage},
    {"start_bit_out_of_range", IssueCode::StartBitOutOfRange},
    {"bit_length_excessive", IssueCode::BitLengthExcessive},
    {"multiplexor_non_unit_scaling", IssueCode::MultiplexorNonUnitScaling},
    {"duplicate_attribute_name", IssueCode::DuplicateAttributeName},
    {"unknown_comment_target", IssueCode::UnknownCommentTarget},
    {"unknown_message_sender", IssueCode::UnknownMessageSender},
    {"unknown_signal_receiver", IssueCode::UnknownSignalReceiver},
    {"unknown_value_description_target", IssueCode::UnknownValueDescriptionTarget},
    {"text_roundtrip_divergence", IssueCode::TextRoundtripDivergence},
    {"multi_value_mux_selector", IssueCode::MultiValueMuxSelector},
    {"mux_master_incoherent", IssueCode::MuxMasterIncoherent},
    {"unknown_attribute_name", IssueCode::UnknownAttributeName},
    {"attribute_value_type_mismatch", IssueCode::AttributeValueTypeMismatch},
    {"attribute_enum_empty", IssueCode::AttributeEnumEmpty},
    {"attribute_enum_default_unstable", IssueCode::AttributeEnumDefaultUnstable},
});

static auto parse_issue_code(std::string_view s) -> IssueCode {
    return lookup(issue_code_table, s).value_or(IssueCode::Unknown);
}

// Parse one validation-issue entry ({severity, code, detail}); shared by the
// validate-response and parsed-DBC-warnings decoders.
static auto parse_issue_entry(const Json& issue) -> Result<ValidationIssue> {
    auto const sev_str = issue.value("severity", "");
    IssueSeverity severity{};
    if (sev_str == "error") {
        severity = IssueSeverity::Error;
    } else if (sev_str == "warning") {
        severity = IssueSeverity::Warning;
    } else {
        return std::unexpected(
            make_error(ErrorKind::Protocol, "Unknown validation severity: " + sev_str));
    }
    auto const code_str = issue.value("code", "");
    return ValidationIssue{
        .severity = severity,
        .code = parse_issue_code(code_str),
        .code_raw = code_str,
        .detail = issue.value("detail", ""),
    };
}

// The same wire shapes in an integer position: the rational must reduce to a
// whole number (parse_rational_dict has already refused a non-positive
// denominator, so the division is safe).
static auto parse_rational_as_int(const Json& j) -> std::int64_t {
    auto const r = parse_rational(j);
    if (r.numerator() % r.denominator() != 0)
        throw std::runtime_error("Non-exact rational in integer field: " + j.dump());
    return r.numerator() / r.denominator();
}

// ---------------------------------------------------------------------------
// DBC parsing (for formatDBC response)
// ---------------------------------------------------------------------------

// Decode the explicit `presence` discriminator the core emits for every signal
// ("always" / "multiplexed") rather than inferring multiplexing from the bare
// presence of a `multiplexor` field (parity with Go/Rust/Python). A multiplexed
// signal requires a non-empty multiplexor and a non-empty multiplex_values array
// of u32 selectors.
static auto parse_signal_presence(const Json& j) -> SignalPresence {
    auto const presence_str = j.value("presence", std::string{});
    if (presence_str == "always")
        return AlwaysPresent{};
    if (presence_str != "multiplexed")
        throw std::runtime_error("unknown signal presence: " + presence_str);
    auto mux_name = j.value("multiplexor", std::string{});
    if (mux_name.empty())
        throw std::runtime_error("multiplexed signal requires a non-empty \"multiplexor\"");
    if (!j.contains("multiplex_values") || !j.at("multiplex_values").is_array() ||
        j.at("multiplex_values").empty())
        throw std::runtime_error(
            "multiplexed signal requires a non-empty \"multiplex_values\" array");
    auto const& arr = j.at("multiplex_values");
    std::vector<MultiplexValue> vals;
    for (auto const& elem : arr) {
        // Read wide, then bound to u32 — nlohmann's get<uint32_t> would silently
        // truncate an out-of-range value rather than reject it.
        auto const v = require_int<std::int64_t>(elem, "multiplex_values entry");
        if (v < 0 || v > 0xFFFF'FFFFLL) // u32 max — parity with Go's MaxUint32 bound
            throw std::runtime_error("multiplex_values entry " + std::to_string(v) +
                                     " out of range (0-4294967295)");
        vals.emplace_back(static_cast<std::uint32_t>(v));
    }
    return Multiplexed{.multiplexor = SignalName{std::move(mux_name)},
                       .multiplex_values = std::move(vals)};
}

// One {value, description} pair; the wire shape of an inline VAL_ entry and of
// a VAL_TABLE_ row.  `context` names the field in a rejection message.
static auto parse_value_entry(const Json& j, std::string_view context) -> DbcValueEntry {
    return DbcValueEntry{
        .value = require_int<std::int64_t>(j.at("value"), context),
        .description = j.at("description").get<std::string>(),
    };
}

static auto parse_signal_def(const Json& j) -> DbcSignal {
    auto const bo_str = j.value("byteOrder", "little_endian");
    ByteOrder bo{};
    if (bo_str == "little_endian")
        bo = ByteOrder::LittleEndian;
    else if (bo_str == "big_endian")
        bo = ByteOrder::BigEndian;
    else
        throw std::runtime_error("Unrecognized byteOrder: " + bo_str);

    auto presence = parse_signal_presence(j);

    auto receivers = parse_optional_array(
        j, "receivers", [](const Json& elem) { return NodeName{elem.get<std::string>()}; });
    auto value_descriptions = parse_optional_array(j, "valueDescriptions", [](const Json& elem) {
        return parse_value_entry(elem, "valueDescriptions value");
    });

    auto const start_bit_raw = require_uint<std::uint32_t>(j.at("startBit"), "startBit");
    if (start_bit_raw > 511)
        throw std::runtime_error("startBit " + std::to_string(start_bit_raw) +
                                 " out of range (0-511)");
    auto const length_raw = require_uint<std::uint32_t>(j.at("length"), "length");
    if (length_raw < 1 || length_raw > 512)
        throw std::runtime_error("bit length " + std::to_string(length_raw) +
                                 " out of range (1-512)");

    return DbcSignal{
        .name = SignalName{j.at("name").get<std::string>()},
        .start_bit = BitPosition{static_cast<std::uint16_t>(start_bit_raw)},
        .bit_length = BitLength{static_cast<std::uint16_t>(length_raw)},
        .byte_order = bo,
        .is_signed = j.value("signed", false),
        .factor = RationalFactor{parse_rational(j.at("factor"))},
        .offset = RationalOffset{parse_rational(j.at("offset"))},
        .minimum = RationalBound{parse_rational(j.at("minimum"))},
        .maximum = RationalBound{parse_rational(j.at("maximum"))},
        .unit = Unit{j.value("unit", "")},
        .presence = std::move(presence),
        .receivers = std::move(receivers),
        .value_descriptions = std::move(value_descriptions),
    };
}

// Construct a typed `CanId` from a JSON `{id, extended}` pair.  Centralises
// the 11-bit standard-frame range check (max 2047) and the typed factory
// failure paths so parse_message_def and parse_raw_value_desc agree on the
// error wording.
static auto json_to_can_id(std::uint32_t id_val, bool extended) -> CanId {
    if (extended) {
        auto result = ExtendedId::create(id_val);
        if (!result)
            throw std::runtime_error("Invalid extended CAN ID " + std::to_string(id_val) + ": " +
                                     result.error());
        return CanId{*result};
    }
    if (id_val > 0x7FFU)
        throw std::runtime_error("Standard CAN ID value " + std::to_string(id_val) +
                                 " exceeds 11-bit standard-frame range (max 2047)");
    auto result = StandardId::create(static_cast<std::uint16_t>(id_val));
    if (!result)
        throw std::runtime_error("Invalid standard CAN ID " + std::to_string(id_val) + ": " +
                                 result.error());
    return CanId{*result};
}

static auto parse_message_def(const Json& j) -> DbcMessage {
    auto const id_val = require_uint<std::uint32_t>(j.at("id"), "message id");
    const bool extended = j.value("extended", false);
    const CanId id = json_to_can_id(id_val, extended);

    auto dlc_result = bytes_to_dlc(require_uint<std::size_t>(j.at("dlc"), "dlc"));
    if (!dlc_result)
        throw std::runtime_error("Invalid DLC: " + dlc_result.error());

    std::vector<DbcSignal> signals;
    for (auto const& s : j.at("signals"))
        signals.push_back(parse_signal_def(s));

    auto senders = parse_optional_array(
        j, "senders", [](const Json& elem) { return NodeName{elem.get<std::string>()}; });

    return DbcMessage{
        .id = id,
        .name = MessageName{j.at("name").get<std::string>()},
        .dlc = *dlc_result,
        .sender = NodeName{j.value("sender", "")},
        .senders = std::move(senders),
        .signals = std::move(signals),
    };
}

static auto parse_signal_group(const Json& j) -> DbcSignalGroup {
    std::vector<SignalName> sigs;
    for (auto const& s : j.at("signals"))
        sigs.emplace_back(s.get<std::string>());
    return DbcSignalGroup{
        .name = j.at("name").get<std::string>(),
        .signals = std::move(sigs),
    };
}

static auto parse_env_var_type(int raw, const std::string& name) -> DbcVarType {
    switch (raw) {
    case 0:
        return DbcVarType::Int;
    case 1:
        return DbcVarType::Float;
    case 2:
        return DbcVarType::String;
    default:
        throw std::runtime_error("Unknown environment variable type " + std::to_string(raw) +
                                 " for '" + name + "'");
    }
}

static auto parse_env_var(const Json& j) -> DbcEnvironmentVar {
    auto const name = j.at("name").get<std::string>();
    auto const raw_type = require_int<int>(j.at("varType"), "varType");
    return DbcEnvironmentVar{
        .name = name,
        .var_type = parse_env_var_type(raw_type, name),
        .initial = parse_rational(j.at("initial")),
        .minimum = parse_rational(j.at("minimum")),
        .maximum = parse_rational(j.at("maximum")),
    };
}

static auto parse_value_table(const Json& j) -> DbcValueTable {
    std::vector<DbcValueEntry> entries;
    for (auto const& e : j.at("entries"))
        entries.push_back(parse_value_entry(e, "valueTable entry value"));
    return DbcValueTable{
        .name = j.at("name").get<std::string>(),
        .entries = std::move(entries),
    };
}

// ---------------------------------------------------------------------------
// Tier 2 parsers (nodes / comments / attributes). Each variant is dispatched
// on the required ``"kind"`` field; unknown values surface as a protocol
// error at the public boundary.
// ---------------------------------------------------------------------------

static auto parse_node(const Json& j) -> DbcNode {
    return DbcNode{.name = NodeName{j.at("name").get<std::string>()}};
}

// The validated identifier a message- or signal-scoped target names. The wire
// carries a value and an optional flag; the target carries the type they
// denote, so an identifier too wide for the width it claims is refused here
// rather than stored and passed on.
static auto parse_target_can_id(const Json& j) -> CanId {
    return json_to_can_id(require_uint<std::uint32_t>(j.at("id"), "CAN id"),
                          j.value("extended", false));
}

static auto parse_comment_target(const Json& j) -> DbcCommentTarget {
    auto const kind = j.at("kind").get<std::string>();
    if (kind == "network")
        return DbcCommentTargetNetwork{};
    if (kind == "node")
        return DbcCommentTargetNode{.node = NodeName{j.at("node").get<std::string>()}};
    if (kind == "message")
        return DbcCommentTargetMessage{.id = parse_target_can_id(j)};
    if (kind == "signal")
        return DbcCommentTargetSignal{.id = parse_target_can_id(j),
                                      .signal = j.at("signal").get<std::string>()};
    if (kind == "envVar")
        return DbcCommentTargetEnvVar{.env_var = j.at("envVar").get<std::string>()};
    throw std::runtime_error("Unknown comment target kind: " + kind);
}

static auto parse_comment(const Json& j) -> DbcComment {
    return DbcComment{
        .target = parse_comment_target(j.at("target")),
        .text = j.at("text").get<std::string>(),
    };
}

// String → DbcAttrScope lookup table.  Same shape as `error_code_table` /
// `issue_code_table`; unknown scope is a hard error (unlike issue_code).
using AttrScopeEntry = std::pair<std::string_view, DbcAttrScope>;
constexpr auto attr_scope_table = std::to_array<AttrScopeEntry>({
    {"network", DbcAttrScope::Network},
    {"node", DbcAttrScope::Node},
    {"message", DbcAttrScope::Message},
    {"signal", DbcAttrScope::Signal},
    {"envVar", DbcAttrScope::EnvVar},
    {"nodeMsg", DbcAttrScope::NodeMsg},
    {"nodeSig", DbcAttrScope::NodeSig},
});

static auto parse_attr_scope(std::string_view s) -> DbcAttrScope {
    if (auto scope = lookup(attr_scope_table, s))
        return *scope;
    throw std::runtime_error("Unknown attribute scope: " + std::string{s});
}

static auto parse_attr_type(const Json& j) -> DbcAttrType {
    auto const kind = j.at("kind").get<std::string>();
    if (kind == "int")
        return DbcAttrTypeInt{.min = require_int<std::int64_t>(j.at("min"), "int attribute min"),
                              .max = require_int<std::int64_t>(j.at("max"), "int attribute max")};
    if (kind == "float")
        return DbcAttrTypeFloat{.min = parse_rational(j.at("min")),
                                .max = parse_rational(j.at("max"))};
    if (kind == "string")
        return DbcAttrTypeString{};
    if (kind == "enum") {
        std::vector<std::string> values;
        for (auto const& v : j.at("values"))
            values.push_back(v.get<std::string>());
        return DbcAttrTypeEnum{.values = std::move(values)};
    }
    if (kind == "hex")
        return DbcAttrTypeHex{.min = require_int<std::int64_t>(j.at("min"), "hex attribute min"),
                              .max = require_int<std::int64_t>(j.at("max"), "hex attribute max")};
    throw std::runtime_error("Unknown attribute type kind: " + kind);
}

static auto parse_attr_value(const Json& j) -> DbcAttrValue {
    auto const kind = j.at("kind").get<std::string>();
    if (kind == "int")
        return DbcAttrValueInt{.value =
                                   require_int<std::int64_t>(j.at("value"), "int attribute value")};
    if (kind == "float")
        return DbcAttrValueFloat{.value = parse_rational(j.at("value"))};
    if (kind == "string")
        return DbcAttrValueString{.value = j.at("value").get<std::string>()};
    if (kind == "enum")
        return DbcAttrValueEnum{
            .value = require_int<std::int64_t>(j.at("value"), "enum attribute value")};
    if (kind == "hex")
        return DbcAttrValueHex{.value =
                                   require_int<std::int64_t>(j.at("value"), "hex attribute value")};
    throw std::runtime_error("Unknown attribute value kind: " + kind);
}

static auto parse_attr_target(const Json& j) -> DbcAttrTarget {
    auto const kind = j.at("kind").get<std::string>();
    if (kind == "network")
        return DbcAttrTargetNetwork{};
    if (kind == "node")
        return DbcAttrTargetNode{.node = NodeName{j.at("node").get<std::string>()}};
    if (kind == "message")
        return DbcAttrTargetMessage{.id = parse_target_can_id(j)};
    if (kind == "signal")
        return DbcAttrTargetSignal{.id = parse_target_can_id(j),
                                   .signal = j.at("signal").get<std::string>()};
    if (kind == "envVar")
        return DbcAttrTargetEnvVar{.env_var = j.at("envVar").get<std::string>()};
    if (kind == "nodeMsg")
        return DbcAttrTargetNodeMsg{.node = NodeName{j.at("node").get<std::string>()},
                                    .id = parse_target_can_id(j)};
    if (kind == "nodeSig")
        return DbcAttrTargetNodeSig{.node = NodeName{j.at("node").get<std::string>()},
                                    .id = parse_target_can_id(j),
                                    .signal = j.at("signal").get<std::string>()};
    throw std::runtime_error("Unknown attribute target kind: " + kind);
}

static auto parse_attribute(const Json& j) -> DbcAttribute {
    auto const kind = j.at("kind").get<std::string>();
    if (kind == "definition")
        return DbcAttrDef{
            .name = j.at("name").get<std::string>(),
            .scope = parse_attr_scope(j.at("scope").get<std::string>()),
            .attr_type = parse_attr_type(j.at("attrType")),
        };
    if (kind == "default")
        return DbcAttrDefault{
            .name = j.at("name").get<std::string>(),
            .value = parse_attr_value(j.at("value")),
        };
    if (kind == "assignment")
        return DbcAttrAssign{
            .name = j.at("name").get<std::string>(),
            .target = parse_attr_target(j.at("target")),
            .value = parse_attr_value(j.at("value")),
        };
    throw std::runtime_error("Unknown attribute kind: " + kind);
}

// Inverse of json_serialize.cpp's raw_value_desc_to_json.
// Reads one unresolved RawValueDesc from the wire — message-id pair (id +
// optional extended) plus signalName + entries array. Wire shape is fixed
// at the cross-binding boundary, mirrored by Python `_normalize_raw_value_desc`
// and Go `parseUnresolvedValueDescs`.
static auto parse_raw_value_desc(const Json& j) -> DbcRawValueDesc {
    auto const id_val = require_uint<std::uint32_t>(j.at("id"), "CAN id");
    const bool extended = j.value("extended", false);
    const CanId can_id = json_to_can_id(id_val, extended);
    std::vector<DbcValueEntry> entries;
    for (auto const& e : j.at("entries"))
        entries.push_back(parse_value_entry(e, "value-description value"));
    return DbcRawValueDesc{
        .can_id = can_id,
        .signal_name = j.at("signalName").get<std::string>(),
        .entries = std::move(entries),
    };
}

static auto parse_dbc_definition(const Json& j) -> DbcDefinition {
    // `messages` is required; every metadata array is optional on the wire and
    // absent reads the same as empty.
    std::vector<DbcMessage> messages;
    for (auto const& m : j.at("messages"))
        messages.push_back(parse_message_def(m));
    return DbcDefinition{
        .version = j.value("version", ""),
        .messages = std::move(messages),
        .signal_groups = parse_optional_array(j, "signalGroups", parse_signal_group),
        .environment_vars = parse_optional_array(j, "environmentVars", parse_env_var),
        .value_tables = parse_optional_array(j, "valueTables", parse_value_table),
        .nodes = parse_optional_array(j, "nodes", parse_node),
        .comments = parse_optional_array(j, "comments", parse_comment),
        .attributes = parse_optional_array(j, "attributes", parse_attribute),
        .unresolved_value_descs =
            parse_optional_array(j, "unresolvedValueDescs", parse_raw_value_desc),
    };
}

// ---------------------------------------------------------------------------
// Public parsing functions
//
// Each function catches exceptions from JSON access and validated-type
// construction, converting them to Result<> errors at the public boundary.
// ---------------------------------------------------------------------------

auto parse_success(std::string_view input) -> Result<void> {
    try {
        auto const j = parse_bounded(input);
        auto const status = j.value("status", "");
        if (status == "success")
            return {};
        if (status == "error")
            return std::unexpected(make_json_error(ErrorKind::Protocol, j));
        return std::unexpected(make_error(ErrorKind::Protocol, "Unexpected status: " + status));
    } catch (const std::exception& e) {
        return std::unexpected(make_error(ErrorKind::Protocol, e.what()));
    }
}

auto parse_event_ack(std::string_view input) -> Result<void> {
    try {
        auto const j = parse_bounded(input);
        auto const status = j.value("status", "");
        if (status == "ack")
            return {};
        if (status == "error")
            return std::unexpected(make_json_error(ErrorKind::Protocol, j));
        return std::unexpected(make_error(ErrorKind::Protocol, "Unexpected status: " + status));
    } catch (const std::exception& e) {
        return std::unexpected(make_error(ErrorKind::Protocol, e.what()));
    }
}

auto parse_validation(std::string_view input) -> Result<ValidationResult> {
    try {
        auto j = parse_bounded(input);
        auto const status = j.value("status", "");
        if (status == "error")
            return std::unexpected(make_json_error(ErrorKind::Validation, j));
        if (status != "validation")
            return std::unexpected(make_error(ErrorKind::Protocol, "Expected validation response"));

        std::vector<ValidationIssue> issues;
        for (auto const& issue : j.at("issues")) {
            auto entry = parse_issue_entry(issue);
            if (!entry)
                return std::unexpected(entry.error());
            issues.push_back(std::move(*entry));
        }
        return ValidationResult{
            .has_errors = j.value("has_errors", false),
            .issues = std::move(issues),
        };
    } catch (const std::exception& e) {
        return std::unexpected(make_error(ErrorKind::Protocol, e.what()));
    }
}

auto parse_extraction(std::string_view input) -> Result<ExtractionResult> {
    try {
        auto const j = parse_bounded(input);
        auto const status = j.value("status", "");
        if (status == "error")
            return std::unexpected(make_json_error(ErrorKind::Protocol, j));
        if (status != "success")
            return std::unexpected(
                make_error(ErrorKind::Protocol, "Unexpected extraction status: " + status));

        std::vector<SignalValue> values;
        for (auto const& v : j.value("values", Json::array()))
            values.push_back({.name = SignalName{v.at("name").get<std::string>()},
                              .value = PhysicalValue{parse_rational(v.at("value"))}});

        std::vector<SignalError> errors;
        for (auto const& e : j.value("errors", Json::array()))
            errors.push_back({.name = SignalName{e.at("name").get<std::string>()},
                              .reason = e.value("error", "")});

        std::vector<SignalName> absent;
        for (auto const& a : j.value("absent", Json::array()))
            absent.emplace_back(a.get<std::string>());

        return ExtractionResult{
            .values = std::move(values),
            .errors = std::move(errors),
            .absent = std::move(absent),
        };
    } catch (const std::exception& e) {
        return std::unexpected(make_error(ErrorKind::Protocol, e.what()));
    }
}

auto parse_frame_data(std::string_view input) -> Result<FramePayload> {
    try {
        auto j = parse_bounded(input);
        auto const status = j.value("status", "");
        if (status == "error")
            return std::unexpected(make_json_error(ErrorKind::Protocol, j));
        if (status != "success")
            return std::unexpected(
                make_error(ErrorKind::Protocol, "Unexpected frame data status: " + status));

        auto const& data = j.at("data");
        FramePayload payload;
        for (auto const& byte_val : data)
            payload.push_back(
                static_cast<std::byte>(require_uint<std::uint8_t>(byte_val, "frame data byte")));
        return payload;
    } catch (const std::exception& e) {
        return std::unexpected(make_error(ErrorKind::Protocol, e.what()));
    }
}

// Parse one inner per-property verdict object — shared between the
// streaming PropertyBatch path (frame response) and the EndStream
// StreamResult path (parse_stream_result).
static auto parse_property_result_entry(const Json& r) -> PropertyResult {
    auto const entry_status = r.value("status", "");
    Verdict verdict{};
    if (entry_status == "holds")
        verdict = Verdict::Holds;
    else if (entry_status == "fails")
        verdict = Verdict::Fails;
    else if (entry_status == "unresolved")
        verdict = Verdict::Unresolved;
    else
        throw std::runtime_error("Unknown verdict status: " + entry_status);
    auto idx = parse_rational_as_int(r.at("property_index"));
    if (idx < 0)
        throw std::runtime_error("Negative property_index: " + std::to_string(idx));

    std::optional<Timestamp> ts;
    if (r.contains("timestamp")) {
        auto ts_val = parse_rational_as_int(r.at("timestamp"));
        if (ts_val < 0)
            throw std::runtime_error("Negative timestamp: " + std::to_string(ts_val));
        ts = Timestamp{ts_val};
    }

    std::string reason;
    if (r.contains("reason") && r.at("reason").is_string())
        reason = r.at("reason").get<std::string>();

    return PropertyResult{
        .property_index = PropertyIndex{static_cast<std::size_t>(idx)},
        .verdict = verdict,
        .timestamp = ts,
        .reason = std::move(reason),
    };
}

auto parse_frame_response(std::string_view input) -> Result<FrameResponse> {
    // Fast path: byte-level check for the common ack response, which nearly
    // every streaming frame is. Without it the C++ throughput harness reads
    // 4 to 9 percent fewer frames per second on the streaming benchmarks.
    static constexpr std::string_view ack_compact = R"({"status":"ack"})";
    static constexpr std::string_view ack_spaced = R"({"status": "ack"})";
    if (input == ack_compact || input == ack_spaced)
        return FrameResponse{Ack{}};

    try {
        auto j = parse_bounded(input);
        auto const status = j.value("status", "");

        if (status == "ack")
            return FrameResponse{Ack{}};

        if (status == "error")
            return std::unexpected(make_json_error(ErrorKind::Protocol, j));

        // A streaming PropertyResponse is a batch envelope
        // `{"type": "property_batch", "results": [...]}`.  Each results entry
        // is a PropertyResult (holds/fails/unresolved); a violation closes the
        // batch, in source order, per the Agda dispatchIterResult invariant.
        if (j.value("type", "") == "property_batch") {
            auto const& raw_results = j.at("results");
            if (!raw_results.is_array() || raw_results.empty())
                throw std::runtime_error(
                    "property_batch response 'results' must be a non-empty array "
                    "(zero-event frames are encoded as ack)");
            std::vector<PropertyResult> results;
            for (auto const& r : raw_results)
                results.push_back(parse_property_result_entry(r));
            return FrameResponse{PropertyBatch{.results = std::move(results)}};
        }

        return std::unexpected(
            make_error(ErrorKind::Protocol, "Unexpected frame response: status=" + status +
                                                " type=" + j.value("type", "")));
    } catch (const std::exception& e) {
        return std::unexpected(make_error(ErrorKind::Protocol, e.what()));
    }
}

// Parse one entry in the `warnings` array.  Kept apart from
// `parse_stream_result` so that function stays under clang-tidy's
// cognitive-complexity threshold.
static auto parse_stream_warning_entry(const Json& w) -> StreamWarning {
    if (!w.contains("property_index"))
        throw std::runtime_error("Warning entry missing required 'property_index' field");
    auto kind = w.value("kind", "");
    auto idx = parse_rational_as_int(w.at("property_index"));
    if (idx < 0)
        throw std::runtime_error("Negative warning property_index: " + std::to_string(idx));
    auto detail = w.value("detail", "");
    return StreamWarning{
        .kind = std::move(kind),
        .property_index = PropertyIndex{static_cast<std::size_t>(idx)},
        .detail = std::move(detail),
    };
}

auto parse_stream_result(std::string_view input) -> Result<StreamResult> {
    try {
        auto j = parse_bounded(input);
        auto const status = j.value("status", "");

        if (status == "error")
            return std::unexpected(make_json_error(ErrorKind::Protocol, j));
        if (status != "complete")
            return std::unexpected(make_error(ErrorKind::Protocol, "Expected complete response"));

        std::vector<PropertyResult> results;
        for (auto const& r : j.at("results"))
            results.push_back(parse_property_result_entry(r));

        std::vector<StreamWarning> warnings;
        if (j.contains("warnings")) {
            for (auto const& w : j.at("warnings"))
                warnings.push_back(parse_stream_warning_entry(w));
        }
        return StreamResult{.results = std::move(results), .warnings = std::move(warnings)};
    } catch (const std::exception& e) {
        return std::unexpected(make_error(ErrorKind::Protocol, e.what()));
    }
}

auto parse_dbc_response(std::string_view input) -> Result<DbcDefinition> {
    try {
        auto j = parse_bounded(input);
        auto const status = j.value("status", "");
        if (status == "error")
            return std::unexpected(make_json_error(ErrorKind::Protocol, j));
        if (status != "success")
            return std::unexpected(
                make_error(ErrorKind::Protocol, "Unexpected DBC response status: " + status));
        if (!j.contains("dbc"))
            return std::unexpected(
                make_error(ErrorKind::Protocol, "Missing 'dbc' field in response"));
        return parse_dbc_definition(j.at("dbc"));
    } catch (const std::exception& e) {
        return std::unexpected(make_error(ErrorKind::Protocol, e.what()));
    }
}

auto parse_parsed_dbc(std::string_view input) -> Result<ParsedDBC> {
    try {
        auto j = parse_bounded(input);
        auto const status = j.value("status", "");
        if (status == "error")
            return std::unexpected(make_json_error(ErrorKind::Protocol, j));
        if (status != "success")
            return std::unexpected(
                make_error(ErrorKind::Protocol, "Unexpected parsed-DBC status: " + status));
        if (!j.contains("dbc"))
            return std::unexpected(
                make_error(ErrorKind::Protocol, "Missing 'dbc' field in parsed-DBC response"));
        auto dbc = parse_dbc_definition(j.at("dbc"));

        std::vector<ValidationIssue> warnings;
        if (j.contains("warnings")) {
            for (auto const& issue : j.at("warnings")) {
                auto entry = parse_issue_entry(issue);
                if (!entry)
                    return std::unexpected(entry.error());
                warnings.push_back(std::move(*entry));
            }
        }
        return ParsedDBC{.dbc = std::move(dbc), .warnings = std::move(warnings)};
    } catch (const std::exception& e) {
        return std::unexpected(make_error(ErrorKind::Protocol, e.what()));
    }
}

auto parse_dbc_text_response(std::string_view input) -> Result<DbcText> {
    try {
        auto j = parse_bounded(input);
        auto const status = j.value("status", "");
        if (status == "error")
            return std::unexpected(make_json_error(ErrorKind::Protocol, j));
        if (status != "success")
            return std::unexpected(make_error(
                ErrorKind::Protocol, "Unexpected formatDBCText response status: " + status));
        if (!j.contains("text") || !j.at("text").is_string())
            return std::unexpected(
                make_error(ErrorKind::Protocol,
                           "Missing or non-string 'text' field in formatDBCText response"));
        // Absent issues → empty; a present-but-non-array issues field is a
        // protocol error, not silently harvested (nlohmann range-for over an
        // object would iterate its values).  Parity with the Python/Go/Rust
        // decoders; mirrors the is_array() guard in lift_validation_issues.
        std::vector<ValidationIssue> issues;
        if (j.contains("issues")) {
            if (!j.at("issues").is_array())
                return std::unexpected(make_error(
                    ErrorKind::Protocol, "'issues' must be an array in formatDBCText response"));
            for (auto const& issue : j.at("issues")) {
                auto entry = parse_issue_entry(issue);
                if (!entry)
                    return std::unexpected(entry.error());
                issues.push_back(std::move(*entry));
            }
        }
        return DbcText{.text = j.at("text").get<std::string>(), .issues = std::move(issues)};
    } catch (const std::exception& e) {
        return std::unexpected(make_error(ErrorKind::Protocol, e.what()));
    }
}

} // namespace aletheia::detail

namespace aletheia {

// Public issue-rendering helpers (declared in <aletheia/validation.hpp>).
// Inverse of the parser's string→enum mapping; reuse the same
// `issue_code_table` so codes round-trip exactly.
auto to_string(IssueSeverity severity) -> std::string_view {
    switch (severity) {
    case IssueSeverity::Error:
        return "error";
    case IssueSeverity::Warning:
        return "warning";
    }
    return "unknown";
}

auto to_string(IssueCode code) -> std::string_view {
    for (auto const& [name, c] : detail::issue_code_table)
        if (c == code)
            return name;
    return "unknown";
}

auto issue_code_label(const ValidationIssue& issue) -> std::string_view {
    // Preserve the original wire string for an unrecognized code so a future
    // core code round-trips instead of degrading to the literal "unknown".
    if (issue.code == IssueCode::Unknown && !issue.code_raw.empty())
        return issue.code_raw;
    return to_string(issue.code);
}

} // namespace aletheia
