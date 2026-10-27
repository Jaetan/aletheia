// SPDX-FileCopyrightText: 2025 Nicolas Pelletier
// SPDX-License-Identifier: BSD-2-Clause
// JSON parsing: Agda core response strings → C++ types.
#include "detail/bad_alloc.hpp"
#include "detail/json.hpp"
#include "detail/json_parse_helpers.hpp"

#include <aletheia/detail/checked.hpp>
#include <aletheia/limits.hpp>

#include <nlohmann/json.hpp>

#include <array>
#include <cstddef>
#include <cstdint>
#include <exception>
#include <expected>
#include <optional>
#include <stdexcept>
#include <string>
#include <string_view>
#include <utility>
#include <vector>

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
    {"parse_dlc_code_out_of_range", ErrorCode::ParseDlcCodeOutOfRange},
    {"parse_payload_length_mismatch", ErrorCode::ParsePayloadLengthMismatch},
    {"parse_payload_byte_out_of_range", ErrorCode::ParsePayloadByteOutOfRange},
    {"parse_non_positive_denominator", ErrorCode::ParseNonPositiveDenominator},
    {"parse_signal_array_length_mismatch", ErrorCode::ParseSignalArrayLengthMismatch},
    {"parse_timestamp_past_wire", ErrorCode::ParseTimestampPastWire},
    // Text parse errors: a .dbc text, or a decimal literal, read by the same grammar machinery
    {"text_parse_failure", ErrorCode::TextParseFailure},
    {"text_trailing_input", ErrorCode::TextTrailingInput},
    {"dbc_text_attribute_refinement_failed", ErrorCode::DBCTextAttributeRefinementFailed},
    // Frame errors
    {"frame_signal_not_found", ErrorCode::FrameSignalNotFound},
    {"frame_signal_index_oob", ErrorCode::FrameSignalIndexOob},
    {"frame_value_out_of_range", ErrorCode::FrameValueOutOfRange},
    {"frame_value_not_representable", ErrorCode::FrameValueNotRepresentable},
    {"frame_signals_overlap", ErrorCode::FrameSignalsOverlap},
    {"frame_signal_past_frame_end", ErrorCode::FrameSignalPastFrameEnd},
    {"frame_can_id_not_found", ErrorCode::FrameCanIdNotFound},
    {"frame_can_id_mismatch", ErrorCode::FrameCanIdMismatch},
    {"frame_signal_value_out_of_bounds", ErrorCode::FrameSignalValueOutOfBounds},
    // Top-level adversarial-input bound
    {"input_bound_exceeded", ErrorCode::InputBoundExceeded},
    // The DBC character set and keywords
    {"dbc_invalid_character", ErrorCode::DBCInvalidCharacter},
    {"dbc_keyword_name", ErrorCode::DBCKeywordName},
    // Route errors
    {"route_missing_field", ErrorCode::RouteMissingField},
    {"route_unknown_command", ErrorCode::RouteUnknownCommand},
    {"route_missing_command_field", ErrorCode::RouteMissingCommandField},
    {"route_missing_dbc_field", ErrorCode::RouteMissingDbcField},
    {"route_missing_props_field", ErrorCode::RouteMissingPropsField},
    // Handler errors
    {"handler_no_dbc", ErrorCode::HandlerNoDbc},
    {"handler_already_streaming", ErrorCode::HandlerAlreadyStreaming},
    {"handler_not_streaming", ErrorCode::HandlerNotStreaming},
    {"handler_stream_not_started", ErrorCode::HandlerStreamNotStarted},
    {"handler_stream_active", ErrorCode::HandlerStreamActive},
    {"handler_property_parse_failed", ErrorCode::HandlerPropertyParseFailed},
    {"handler_unknown_signal", ErrorCode::HandlerUnknownSignal},
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
    {"extraction_signal_past_frame_end", ErrorCode::ExtractionSignalPastFrameEnd},
    {"extraction_mux_signal_not_found", ErrorCode::ExtractionMuxSignalNotFound},
    {"extraction_mux_chain_cycle", ErrorCode::ExtractionMuxChainCycle},
    {"extraction_mux_extraction_failed", ErrorCode::ExtractionMuxExtractionFailed},
    {"extraction_value_exceeds_wire_range", ErrorCode::ExtractionValueExceedsWireRange},
    // The shared library's own refusal
    {"ffi_validation_error", ErrorCode::FfiValidationError},
});

} // namespace

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
// any `BoundKind` and the typed shape would be misleading.  wire_guarded,
// which every parse_* runs inside, converts the `runtime_error` to a Protocol
// `Result<>` error, the right semantic class (malformed/corrupted server reply).
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
// bound_info lift, lift_bound_info.
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
            issues.push_back(std::move(entry).value());
        }
    } catch (const Json::exception&) {
        // A non-object element or an ill-typed field throws from nlohmann's
        // value(); degrade identically to a failed entry parse. Nothing else is
        // caught: a check of this file's own that stops firing propagates.
        return std::nullopt;
    }
    return issues;
}

// Lift the structured `bound_kind / observed / limit` triple, and the `field`
// a DBC size bound adds, from an input_bound_exceeded envelope.  The triple
// must be present and well-typed, and `field` absent or a string, for the lift
// to populate; anything else degrades to nullopt rather than to a Protocol
// error, so the AletheiaError still carries kind/code/message.
static auto lift_bound_info(const Json& j) -> std::optional<InputBoundExceededError> {
    if (!j.contains("bound_kind") || !j.at("bound_kind").is_string() || !j.contains("observed") ||
        !j.at("observed").is_number_unsigned() || !j.contains("limit") ||
        !j.at("limit").is_number_unsigned())
        return std::nullopt;
    std::optional<std::string> field;
    if (j.contains("field")) {
        if (!j.at("field").is_string())
            return std::nullopt;
        field = j.at("field").get<std::string>();
    }
    return InputBoundExceededError{
        .bound_kind = j.at("bound_kind").get<std::string>(),
        .observed = j.at("observed").get<std::uint64_t>(),
        .limit = j.at("limit").get<std::uint64_t>(),
        .field = std::move(field),
    };
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
    std::optional<InputBoundExceededError> bound_info;
    if (effective_kind == ErrorKind::InputBoundExceeded)
        bound_info = lift_bound_info(j);
    std::optional<std::vector<ValidationIssue>> issues;
    if (code == ErrorCode::HandlerValidationFailed || code == ErrorCode::HandlerTextRoundtripFailed)
        issues = lift_validation_issues(j);
    return AletheiaError{effective_kind, j.at("message").get<std::string>(), code,
                         std::move(bound_info), std::move(issues)};
}

// Decode a JSON {numerator, denominator} object into a Rational, validating
// den > 0.  Caller is responsible for first verifying
// `j.is_object() && j.contains("numerator") && j.contains("denominator")`.
static auto parse_rational_dict(const Json& j) -> Rational {
    auto const num = require_int<std::int64_t>(j.at("numerator"), "rational numerator");
    auto const den = require_int<std::int64_t>(j.at("denominator"), "rational denominator");
    // The kernel emits rationals with a positive denominator (the ℕ⁺ invariant),
    // so a non-positive denominator is a wire-format violation — rejected here
    // rather than silently sign-normalized.  Mirrors Python
    // (extract_rational_from_dict), Go (parseRational), and Rust (Rational::new),
    // which all reject den <= 0 at the wire instead of rewriting it, so a
    // malformed payload surfaces rather than hiding.
    auto const rational = Rational::make(num, den);
    if (!rational)
        throw std::runtime_error("Non-positive denominator in rational: " + j.dump());
    return rational.value();
}

// Decode a binary-output entry's refusal envelope (declared in detail/json.hpp)
// with the JSON path's own `make_json_error`, so the code, the message and any
// structured fields surface as they do on a JSON response.
auto binary_refusal(std::string_view envelope, ErrorKind coded) -> AletheiaError {
    try {
        auto const j = parse_bounded(envelope);
        if (j.value("status", "") != "error")
            return make_error(ErrorKind::Protocol,
                              "Error envelope without status \"error\": " + std::string{envelope});
        return make_json_error(coded, j);
    } catch (const std::exception& e) {
        rethrow_if_bad_alloc(e);
        return make_error(ErrorKind::Protocol,
                          "Malformed error envelope " + std::string{envelope} + ": " + e.what());
    }
}

// Agda emits an exact rational as an integer or as
// {"numerator": n, "denominator": d}.  A bare float is rejected: the wire
// carries exact rationals only, so a float is a wire-format violation rather
// than a value to approximate, which is how the Go, Rust and Python decoders
// treat it too.  Throws on any other shape; callers catch at the public API
// boundary.
auto parse_rational(const Json& j) -> Rational {
    if (j.is_number_integer())
        return Rational::integer(require_int<std::int64_t>(j, "rational integer"));
    // contains() answers false on anything but an object, so it is the one test.
    if (j.contains("numerator") && j.contains("denominator"))
        return parse_rational_dict(j);
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
    {"range_exceeds_bits", IssueCode::RangeExceedsBits},
});

static auto parse_issue_code(std::string_view s) -> IssueCode {
    return lookup(issue_code_table, s).value_or(IssueCode::Unknown);
}

// Parse one validation-issue entry ({severity, code, detail}); shared by the
// validate-response and parsed-DBC-warnings decoders.
static auto parse_issue_entry(const Json& issue) -> Result<ValidationIssue> {
    auto const sev_str = issue.value("severity", "");
    constexpr auto severities = std::to_array<std::pair<std::string_view, IssueSeverity>>({
        {"error", IssueSeverity::Error},
        {"warning", IssueSeverity::Warning},
    });
    auto const severity = lookup(severities, sev_str);
    if (!severity)
        return std::unexpected(
            make_error(ErrorKind::Protocol, "Unknown validation severity: " + sev_str));
    auto const code_str = issue.value("code", "");
    return ValidationIssue{
        .severity = severity.value(),
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
// Public parsing functions
//
// Each function runs inside wire_guarded, which answers what JSON access and
// validated-type construction throw as a Protocol error: the text is the
// kernel's reply, so a shape it does not have is a fault of the wire.
// ---------------------------------------------------------------------------

// The Protocol error a parse's exception is, called from the handler so
// std::bad_alloc leaves as it came; one function, whatever the parse.
static auto wire_fault(const std::exception& e) -> std::unexpected<AletheiaError> {
    rethrow_if_bad_alloc(e);
    return std::unexpected(make_error(ErrorKind::Protocol, e.what()));
}

template<typename Parse>
static auto wire_guarded(Parse parse) -> decltype(parse()) {
    try {
        return parse();
    } catch (const std::exception& e) {
        return wire_fault(e);
    }
}

auto parse_success(std::string_view input) -> Result<void> {
    return wire_guarded([&] -> Result<void> {
        auto const j = parse_bounded(input);
        auto const status = j.value("status", "");
        if (status == "success")
            return {};
        if (status == "error")
            return std::unexpected(make_json_error(ErrorKind::Protocol, j));
        return std::unexpected(make_error(ErrorKind::Protocol, "Unexpected status: " + status));
    });
}

auto parse_event_ack(std::string_view input) -> Result<void> {
    return wire_guarded([&] -> Result<void> {
        auto const j = parse_bounded(input);
        auto const status = j.value("status", "");
        if (status == "ack")
            return {};
        if (status == "error")
            return std::unexpected(make_json_error(ErrorKind::Protocol, j));
        return std::unexpected(make_error(ErrorKind::Protocol, "Unexpected status: " + status));
    });
}

auto parse_validation(std::string_view input) -> Result<ValidationResult> {
    return wire_guarded([&] -> Result<ValidationResult> {
        auto const j = parse_bounded(input);
        auto const status = j.value("status", "");
        if (status == "error")
            return std::unexpected(make_json_error(ErrorKind::Validation, j));
        if (status != "validation")
            return std::unexpected(make_error(ErrorKind::Protocol, "Expected validation response"));

        std::vector<ValidationIssue> issues;
        for (auto const& issue : j.at("issues")) {
            auto entry = parse_issue_entry(issue);
            if (!entry)
                return std::unexpected(detail::error_of(entry));
            issues.push_back(std::move(entry).value());
        }
        return ValidationResult{
            .has_errors = j.value("has_errors", false),
            .issues = std::move(issues),
        };
    });
}

auto parse_extraction(std::string_view input) -> Result<ExtractionResult> {
    return wire_guarded([&] -> Result<ExtractionResult> {
        auto const j = parse_bounded(input);
        auto const status = j.value("status", "");
        if (status == "error")
            return std::unexpected(make_json_error(ErrorKind::Protocol, j));
        if (status != "success")
            return std::unexpected(
                make_error(ErrorKind::Protocol, "Unexpected extraction status: " + status));

        std::vector<SignalValue> values;
        for (auto const& v : j.value("values", Json::array()))
            values.emplace_back(SignalName{v.at("name").get<std::string>()},
                                PhysicalValue{parse_rational(v.at("value"))});

        std::vector<SignalError> errors;
        for (auto const& e : j.value("errors", Json::array()))
            errors.emplace_back(SignalName{e.at("name").get<std::string>()}, e.value("error", ""));

        std::vector<SignalName> absent;
        for (auto const& a : j.value("absent", Json::array()))
            absent.emplace_back(a.get<std::string>());

        return ExtractionResult{
            .values = std::move(values),
            .errors = std::move(errors),
            .absent = std::move(absent),
        };
    });
}

auto parse_frame_data(std::string_view input) -> Result<FramePayload> {
    return wire_guarded([&] -> Result<FramePayload> {
        auto const j = parse_bounded(input);
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
    });
}

// Parse one inner per-property verdict object — shared between the
// streaming PropertyBatch path (frame response) and the EndStream
// StreamResult path (parse_stream_result).
static auto parse_property_result_entry(const Json& r) -> PropertyResult {
    auto const entry_status = r.value("status", "");
    constexpr auto verdicts = std::to_array<std::pair<std::string_view, Verdict>>({
        {"holds", Verdict::Holds},
        {"fails", Verdict::Fails},
        {"unresolved", Verdict::Unresolved},
    });
    auto const verdict = lookup(verdicts, entry_status);
    if (!verdict)
        throw std::runtime_error("Unknown verdict status: " + entry_status);
    auto const idx = parse_rational_as_int(r.at("property_index"));
    if (idx < 0)
        throw std::runtime_error("Negative property_index: " + std::to_string(idx));

    std::optional<Timestamp> ts;
    if (r.contains("timestamp")) {
        auto const ts_val = parse_rational_as_int(r.at("timestamp"));
        if (ts_val < 0)
            throw std::runtime_error("Negative timestamp: " + std::to_string(ts_val));
        ts = Timestamp{ts_val};
    }

    std::string reason;
    if (r.contains("reason") && r.at("reason").is_string())
        reason = r.at("reason").get<std::string>();

    return PropertyResult{
        .property_index = PropertyIndex{static_cast<std::size_t>(idx)},
        .verdict = verdict.value(),
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

    return wire_guarded([&] -> Result<FrameResponse> {
        auto const j = parse_bounded(input);
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
    });
}

// Parse one entry in the `warnings` array.  Kept apart from
// `parse_stream_result` so that function stays under clang-tidy's
// cognitive-complexity threshold.
static auto parse_stream_warning_entry(const Json& w) -> StreamWarning {
    if (!w.contains("property_index"))
        throw std::runtime_error("Warning entry missing required 'property_index' field");
    auto kind = w.value("kind", "");
    auto const idx = parse_rational_as_int(w.at("property_index"));
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
    return wire_guarded([&] -> Result<StreamResult> {
        auto const j = parse_bounded(input);
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
    });
}

auto parse_dbc_response(std::string_view input) -> Result<DbcDefinition> {
    return wire_guarded([&] -> Result<DbcDefinition> {
        auto const j = parse_bounded(input);
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
    });
}

auto parse_parsed_dbc(std::string_view input) -> Result<ParsedDBC> {
    return wire_guarded([&] -> Result<ParsedDBC> {
        auto const j = parse_bounded(input);
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
                    return std::unexpected(detail::error_of(entry));
                warnings.push_back(std::move(entry).value());
            }
        }
        return ParsedDBC{.dbc = std::move(dbc), .warnings = std::move(warnings)};
    });
}

auto parse_dbc_text_response(std::string_view input) -> Result<DbcText> {
    return wire_guarded([&] -> Result<DbcText> {
        auto const j = parse_bounded(input);
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
                    return std::unexpected(detail::error_of(entry));
                issues.push_back(std::move(entry).value());
            }
        }
        return DbcText{.text = j.at("text").get<std::string>(), .issues = std::move(issues)};
    });
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
