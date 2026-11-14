// SPDX-FileCopyrightText: 2025 Nicolas Pelletier
// SPDX-License-Identifier: BSD-2-Clause
// JSON parsing: Agda core response strings → C++ types.
#include "detail/bad_alloc.hpp"
#include "detail/json.hpp"
#include "detail/json_parse_helpers.hpp"
#include "detail/reply_shape.hpp"
#include "detail/wide_json.hpp"

#include <aletheia/limits.hpp>

#include <nlohmann/json.hpp>

#include <algorithm>
#include <array>
#include <chrono>
#include <cstddef>
#include <cstdint>
#include <exception>
#include <expected>
#include <optional>
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
    {"handler_property_refused", ErrorCode::HandlerPropertyRefused},
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

auto error_code_from_string(std::string_view s) -> std::optional<ErrorCode> {
    return lookup(error_code_table, s);
}

} // namespace aletheia

namespace aletheia::detail {

// Every reader below requires each key the kernel writes and reads each place
// by kind only, refusing what the kernel never writes there in the one form of
// detail/reply_shape.hpp: the ranges and the tags are the kernel's, proven of
// every reply. An issue's severity and code, an error reply's code, a property
// result's type and status and a stream warning's kind are each refused outside
// their set.

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
    {"value_description_key_out_of_range", IssueCode::ValueDescriptionKeyOutOfRange},
});

// The severities the kernel writes.
constexpr auto severity_table = std::to_array<std::pair<std::string_view, IssueSeverity>>({
    {"error", IssueSeverity::Error},
    {"warning", IssueSeverity::Warning},
});

// One validation issue at `path`: its code, one of the issue codes, its detail
// string and its severity, one of the severities.
static auto read_issue(Json const& issue, ReplyPath const& path) -> ValidationIssue {
    auto const code = field_member(issue, path, "code", issue_code_table, expect_issue_code);
    auto detail = field_string(issue, path, "detail");
    auto const severity = field_member(issue, path, "severity", severity_table);
    return ValidationIssue{.severity = severity, .code = code, .detail = std::move(detail)};
}

// The issues at `key` of a reply's root: a validation reply's, a DBC
// refusal's, a parsed DBC's warnings or a DBC text's issues.
static auto read_issues(Json const& reply, std::string_view key) -> std::vector<ValidationIssue> {
    return field_objects(reply, ReplyPath{}, key, read_issue);
}

namespace {

// The has_errors flag and the issues an envelope carries, a validation reply
// or a DBC refusal, both of which the kernel writes on it.
struct IssuesPayload {
    std::vector<ValidationIssue> issues;
    bool has_errors = false;
};

} // namespace

static auto read_issues_payload(Json const& reply) -> IssuesPayload {
    auto const has_errors = field_bool(reply, ReplyPath{}, "has_errors");
    return IssuesPayload{.issues = read_issues(reply, "issues"), .has_errors = has_errors};
}

// The keys of a bound refusal's triple.
constexpr auto bound_triple_keys =
    std::to_array<std::string_view>({"bound_kind", "observed", "limit"});

// The bound a refusal says was crossed, nullopt for an envelope of another
// code. An envelope of any code holding part of the triple holds it whole,
// with a string `field` if it names one, and a bound refusal holds the triple
// always; each broken key is refused at its place. The kernel proves the
// observed size and the limit positive, so they are read with no range check.
static auto read_bound_info(Json const& envelope, ErrorCode code)
    -> std::optional<InputBoundExceededError> {
    ReplyPath const root;
    auto const held = std::ranges::any_of(
        bound_triple_keys, [&](std::string_view key) { return envelope.contains(key); });
    if (!held) {
        if (code == ErrorCode::InputBoundExceeded)
            throw reply_refusal(root.at("bound_kind"), expect_string, came(envelope, "bound_kind"));
        return std::nullopt;
    }
    auto bound = InputBoundExceededError{
        .bound_kind = field_string(envelope, root, "bound_kind"),
        .observed = field_uint128(envelope, root, "observed"),
        .limit = field_uint128(envelope, root, "limit"),
        .field = envelope.contains("field") ? std::optional{field_string(envelope, root, "field")}
                                            : std::nullopt,
    };
    if (code != ErrorCode::InputBoundExceeded)
        return std::nullopt;
    return bound;
}

// The error an error envelope carries, its code, one of the error codes, and
// its message string. It is typed `kind` unless its code names its own: a
// bound refusal is InputBoundExceeded with its bound, as the Python and Go
// bindings' typed input-bound errors are, and a round-trip refusal
// TextRoundtrip, so a caller tells it from a structural validation failure by
// kind(). A validation or round-trip refusal carries its issues, the element
// shape of a validation reply. A place of the envelope holding what the kernel
// never writes there is refused.
static auto envelope_error(Json const& envelope, ErrorKind kind) -> AletheiaError {
    ReplyPath const root;
    auto const code = field_member(envelope, root, "code", error_code_table, expect_error_code);
    auto message = field_string(envelope, root, "message");
    auto bound_info = read_bound_info(envelope, code);
    std::optional<std::vector<ValidationIssue>> issues;
    if (code == ErrorCode::HandlerValidationFailed || code == ErrorCode::HandlerTextRoundtripFailed)
        issues = read_issues_payload(envelope).issues;
    auto effective_kind = kind;
    if (code == ErrorCode::InputBoundExceeded)
        effective_kind = ErrorKind::InputBoundExceeded;
    if (code == ErrorCode::HandlerTextRoundtripFailed)
        effective_kind = ErrorKind::TextRoundtrip;
    return AletheiaError{effective_kind, std::move(message), code, std::move(bound_info),
                         std::move(issues)};
}

// Decode a binary-output entry's refusal envelope (declared in detail/json.hpp)
// as the JSON path decodes an error reply, so the code, the message and any
// structured fields surface as they do on a JSON response. Text that is not an
// envelope, or an envelope that is not an error, is the library malfunctioning,
// refused in the form of every reply place, which names no entry.
auto binary_refusal(std::string_view envelope, ErrorKind coded) -> AletheiaError {
    try {
        auto const reply = read_reply(envelope);
        field_status(reply, ReplyPath{}, "status", {ReplyStatus::Error});
        return envelope_error(reply, coded);
    } catch (std::exception const& e) {
        rethrow_if_bad_alloc(e);
        return AletheiaError{ErrorKind::Protocol, e.what()};
    }
}

// ---------------------------------------------------------------------------
// Public parsing functions
//
// Each function runs inside wire_guarded, which answers what a reader throws
// as a Protocol error: the text is the kernel's reply, so a shape it does not
// have is a fault of the wire.
// ---------------------------------------------------------------------------

// The Protocol error a parse's exception is, called from the handler so
// std::bad_alloc leaves as it came; one function, whatever the parse.
static auto wire_fault(std::exception const& e) -> std::unexpected<AletheiaError> {
    rethrow_if_bad_alloc(e);
    return std::unexpected(AletheiaError{ErrorKind::Protocol, e.what()});
}

template<typename Parse>
static auto wire_guarded(Parse parse) -> decltype(parse()) {
    try {
        return parse();
    } catch (std::exception const& e) {
        return wire_fault(e);
    }
}

// The reply `raw` holds when its status is `want`; an error reply is the error
// it carries, typed `kind` unless its code names its own. Every parser below
// but the frame response's opens with it, so a reply that is malformed, an
// error, or not the answer to the command asked is refused in one place.
static auto decode_reply(std::string_view raw, ReplyStatus want, ErrorKind kind) -> Result<Json> {
    auto reply = read_reply(raw);
    if (field_status(reply, ReplyPath{}, "status", {want, ReplyStatus::Error}) ==
        ReplyStatus::Error)
        return std::unexpected(envelope_error(reply, kind));
    return reply;
}

auto parse_success(std::string_view input) -> Result<void> {
    return wire_guarded([&] -> Result<void> {
        return decode_reply(input, ReplyStatus::Success, ErrorKind::Protocol)
            .transform([](Json const& /*reply*/) {});
    });
}

auto parse_event_ack(std::string_view input) -> Result<void> {
    return wire_guarded([&] -> Result<void> {
        return decode_reply(input, ReplyStatus::Ack, ErrorKind::Protocol)
            .transform([](Json const& /*reply*/) {});
    });
}

auto parse_validation(std::string_view input) -> Result<ValidationResult> {
    return wire_guarded([&] -> Result<ValidationResult> {
        return decode_reply(input, ReplyStatus::Validation, ErrorKind::Validation)
            .transform([](Json const& reply) {
                auto payload = read_issues_payload(reply);
                return ValidationResult{.has_errors = payload.has_errors,
                                        .issues = std::move(payload.issues)};
            });
    });
}

// One extracted value at `path`: the signal's name and its exact value.
static auto read_signal_value(Json const& v, ReplyPath const& path) -> SignalValue {
    return SignalValue{
        .name = SignalName{field_string(v, path, "name")},
        .value = PhysicalValue{field_rational(v, path, "value")},
    };
}

// One extraction error at `path`: the signal's name and the kernel's reason.
static auto read_signal_error(Json const& e, ReplyPath const& path) -> SignalError {
    return SignalError{
        .name = SignalName{field_string(e, path, "name")},
        .reason = field_string(e, path, "error"),
    };
}

auto parse_extraction(std::string_view input) -> Result<ExtractionResult> {
    return wire_guarded([&] -> Result<ExtractionResult> {
        return decode_reply(input, ReplyStatus::Success, ErrorKind::Protocol)
            .transform([](Json const& reply) {
                ReplyPath const root;
                return ExtractionResult{
                    .values = field_objects(reply, root, "values", read_signal_value),
                    .errors = field_objects(reply, root, "errors", read_signal_error),
                    .absent = field_strings<SignalName>(reply, root, "absent"),
                };
            });
    });
}

// A payload out of a JSON reply. Only the mock backend answers this way; the
// library returns the bytes themselves. A number past a byte, which the
// kernel never writes, is refused as the number the place does not hold.
auto parse_frame_data(std::string_view input) -> Result<FramePayload> {
    return wire_guarded([&] -> Result<FramePayload> {
        return decode_reply(input, ReplyStatus::Success, ErrorKind::Protocol)
            .transform([](Json const& reply) {
                ReplyPath const root;
                auto const place = root.at("data");
                FramePayload payload;
                for (auto const& byte : field_array(reply, root, "data"))
                    payload.push_back(
                        static_cast<std::byte>(read_unsigned<std::uint8_t>(byte, place)));
                return payload;
            });
    });
}

// The verdicts the kernel writes.
constexpr auto verdict_table = std::to_array<std::pair<std::string_view, Verdict>>({
    {"fails", Verdict::Fails},
    {"holds", Verdict::Holds},
    {"unresolved", Verdict::Unresolved},
});

// The type, the status and the property index every verdict carries.
static auto read_verdict(Json const& r, ReplyPath const& path) -> PropertyResult {
    field_word(r, path, "type", {"property"});
    auto const verdict = field_member(r, path, "status", verdict_table);
    auto const index = field_unsigned<std::size_t>(r, path, "property_index");
    return PropertyResult{.property_index = PropertyIndex{index}, .verdict = verdict};
}

// The timestamp at `path`, which echoes a frame's: the binding sends every
// timestamp as an int64, so a number past one, which the kernel never writes
// back, is refused as the number the place does not hold.
static auto read_timestamp(Json const& r, ReplyPath const& path) -> Timestamp {
    auto const microseconds = field_unsigned<std::uint64_t>(r, path, "timestamp");
    if (!std::in_range<Timestamp::rep>(microseconds))
        throw reply_refusal(path.at("timestamp"), expect_number, came(r, "timestamp"));
    return Timestamp{static_cast<Timestamp::rep>(microseconds)};
}

// One event of a frame's batch at `path`: its verdict, the timestamp of the
// frame that broke the property on a failure, and a reason on every verdict
// but a hold.
static auto read_property_event(Json const& r, ReplyPath const& path) -> PropertyResult {
    auto result = read_verdict(r, path);
    if (result.verdict == Verdict::Fails)
        result.timestamp = read_timestamp(r, path);
    if (result.verdict != Verdict::Holds)
        result.reason = field_string(r, path, "reason");
    return result;
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
        auto const reply = read_reply(input);
        ReplyPath const root;
        // A batch carries no status of its own, each of its events carrying
        // one, and is told by its type.
        if (reply.contains("status")) {
            if (field_status(reply, root, "status", {ReplyStatus::Ack, ReplyStatus::Error}) ==
                ReplyStatus::Ack)
                return FrameResponse{Ack{}};
            return std::unexpected(envelope_error(reply, ErrorKind::Protocol));
        }
        field_word(reply, root, "type", {"property_batch"});
        return FrameResponse{
            PropertyBatch{.results = field_objects(reply, root, "results", read_property_event)}};
    });
}

// One end-of-stream verdict at `path`. A failure carries the timestamp of the
// frame that broke the property, and an unresolved verdict a timestamp only
// where its key holds one: an absent or null key is no timestamp.
static auto read_property_result(Json const& r, ReplyPath const& path) -> PropertyResult {
    auto result = read_verdict(r, path);
    if (result.verdict == Verdict::Holds)
        return result;
    if (result.verdict == Verdict::Fails || holds_non_null(r, "timestamp"))
        result.timestamp = read_timestamp(r, path);
    result.reason = field_string(r, path, "reason");
    return result;
}

// One end-of-stream warning at `path`.
static auto read_stream_warning(Json const& w, ReplyPath const& path) -> StreamWarning {
    field_word(w, path, "kind", {"uncached_atom"});
    return StreamWarning{
        .kind = WarningKind::UncachedAtom,
        .property_index = PropertyIndex{field_unsigned<std::size_t>(w, path, "property_index")},
        .detail = field_string(w, path, "detail"),
    };
}

auto parse_stream_result(std::string_view input) -> Result<StreamResult> {
    return wire_guarded([&] -> Result<StreamResult> {
        return decode_reply(input, ReplyStatus::Complete, ErrorKind::Protocol)
            .transform([](Json const& reply) {
                ReplyPath const root;
                return StreamResult{
                    .results = field_objects(reply, root, "results", read_property_result),
                    .warnings = field_objects(reply, root, "warnings", read_stream_warning),
                };
            });
    });
}

auto parse_dbc_response(std::string_view input) -> Result<DbcDefinition> {
    return wire_guarded([&] -> Result<DbcDefinition> {
        return decode_reply(input, ReplyStatus::Success, ErrorKind::Protocol)
            .transform([](Json const& reply) {
                return parse_dbc_definition(field_object(reply, ReplyPath{}, "dbc"));
            });
    });
}

auto parse_parsed_dbc(std::string_view input) -> Result<ParsedDBC> {
    return wire_guarded([&] -> Result<ParsedDBC> {
        return decode_reply(input, ReplyStatus::Success, ErrorKind::Protocol)
            .transform([](Json const& reply) {
                ReplyPath const root;
                auto const& dbc = field_object(reply, root, "dbc");
                // The warnings are held to an array before the DBC is read, so a
                // reply broken at both is refused at its warnings, as the other
                // bindings refuse it.
                static_cast<void>(field_array(reply, root, "warnings"));
                auto definition = parse_dbc_definition(dbc);
                return ParsedDBC{.dbc = std::move(definition),
                                 .warnings = read_issues(reply, "warnings")};
            });
    });
}

auto parse_dbc_text_response(std::string_view input) -> Result<DbcText> {
    return wire_guarded([&] -> Result<DbcText> {
        return decode_reply(input, ReplyStatus::Success, ErrorKind::Protocol)
            .transform([](Json const& reply) {
                return DbcText{.text = field_string(reply, ReplyPath{}, "text"),
                               .issues = read_issues(reply, "issues")};
            });
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

} // namespace aletheia
