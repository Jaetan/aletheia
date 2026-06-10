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
#include <utility>
#include <vector>

using Json = nlohmann::json;

namespace aletheia {

namespace {

// String → ErrorCode lookup table. Grouped by error family for readability;
// the order within each group mirrors the Agda error ADTs. Linear scan is fine
// for the 59-entry table on a cold parse path.
using ErrorCodeEntry = std::pair<std::string_view, ErrorCode>;
constexpr std::array<ErrorCodeEntry, 59> error_code_table{{
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
    {"parse_signal_overflows_frame", ErrorCode::ParseSignalOverflowsFrame},
    {"parse_signal_msb_below_bit_length", ErrorCode::ParseSignalMsbBelowBitLength},
    {"parse_invalid_kind", ErrorCode::ParseInvalidKind},
    {"parse_non_terminating_rational", ErrorCode::ParseNonTerminatingRational},
    {"parse_invalid_identifier", ErrorCode::ParseInvalidIdentifier},
    {"parse_non_integer_multiplex_value", ErrorCode::ParseNonIntegerMultiplexValue},
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
    // Top-level adversarial-input bound (R19 cluster 14 / AGDA-C-6.2)
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
}};

} // namespace

auto error_code_from_string(std::string_view s) -> ErrorCode {
    for (const auto& [name, code] : error_code_table)
        if (name == s)
            return code;
    return ErrorCode::Unknown;
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
// rule "Adversarial-input bounds at parser surfaces" + R18 cluster 2 closure.
//
// Throws `std::runtime_error` (not typed `InputBoundExceeded`) by design:
// `InputBoundExceeded` carries the kernel-side `bound_kind / observed / limit`
// triple where `bound_kind` is one of the kernel's `BoundKind` ADT entries
// (`MessageCount`, `AtomCount`, `IdentifierLength`, `PropertyCount`, etc.).
// JSON nesting depth is a client-side guard against malformed *responses*
// from the kernel — not an inbound kernel input bound — so it doesn't fit
// any `BoundKind` and the typed shape would be misleading.  The existing
// `catch (const std::exception&)` block at every parse_* callsite converts
// the `runtime_error` to a `Result<>` error via `make_error(ErrorKind::Protocol,
// ...)`, which is the right semantic class (malformed/corrupted server reply).
static auto parse_bounded(std::string_view input) -> Json {
    auto callback = [](int depth, Json::parse_event_t /*event*/, Json& /*parsed*/) -> bool {
        if (static_cast<std::uint64_t>(depth) > max_nesting_depth) {
            throw std::runtime_error("JSON nesting depth " + std::to_string(depth) +
                                     " exceeds limit " + std::to_string(max_nesting_depth));
        }
        return true;
    };
    return Json::parse(input, callback);
}

// Post-R19P2-cluster-14: routes the response through `ErrorKind::InputBoundExceeded`
// regardless of the kind the caller guessed from the response section (Protocol /
// Validation), so the typed bound-info shape is exposed uniformly across the JSON /
// DBC-text / binary parser surfaces.  Mirrors Python's `InputBoundExceededError`
// subclassing and Go's typed `*InputBoundExceededError` discriminator.  Originally
// dispatched over three codes; cluster 14 collapsed Parse/Route/Handler input-bound
// variants into a single top-level `ErrorCode::InputBoundExceeded`.
static auto is_input_bound_exceeded_code(ErrorCode code) -> bool {
    return code == ErrorCode::InputBoundExceeded;
}

/// Extract error from a JSON response with status=="error", parsing the code field.
///
/// Both ``code`` and ``message`` must be non-null strings — a missing or
/// non-string value surfaces as a ``Protocol`` error rather than being
/// papered over with a default. Matches Python's ``build_error_response``
/// strict contract; R16 shipped with a silent "unknown error code"
/// regression in production logs because the old ``j.value("code", "")``
/// / ``j.value("message", "Unknown error")`` defaults masked malformed
/// responses.
static auto make_json_error(ErrorKind kind, const Json& j) -> AletheiaError {
    if (!j.contains("code") || !j.at("code").is_string())
        return make_error(ErrorKind::Protocol, "Error response missing or non-string 'code' field");
    if (!j.contains("message") || !j.at("message").is_string())
        return make_error(ErrorKind::Protocol,
                          "Error response missing or non-string 'message' field");
    auto code = error_code_from_string(j.at("code").get<std::string>());
    auto effective_kind = is_input_bound_exceeded_code(code) ? ErrorKind::InputBoundExceeded : kind;
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
    return AletheiaError{effective_kind, j.at("message").get<std::string>(), code,
                         std::move(bound_info)};
}

// Decode a JSON {numerator, denominator} object into a normalized (num, den)
// pair with den > 0.  Throws on zero denominator or normalization overflow
// (INT64_MIN cannot be negated).  Caller is responsible for first verifying
// `j.is_object() && j.contains("numerator") && j.contains("denominator")`.
static auto parse_rational_dict(const Json& j) -> std::pair<std::int64_t, std::int64_t> {
    auto num = j.at("numerator").get<std::int64_t>();
    auto den = j.at("denominator").get<std::int64_t>();
    // Branch on sign first: a negative denominator is normalized (num/den both
    // negated, with the asymmetric INT64_MIN guard); a zero denominator is
    // rejected in the non-negative arm.  Ordering the den == 0 check after the
    // den < 0 branch keeps the "< 0" boundary observable — routing den == 0
    // through normalization would yield {num, 0}, which every caller rejects
    // (Rational ctor) or crashes on (num % 0), distinct from this clean throw.
    if (den < 0) {
        if (num == std::numeric_limits<std::int64_t>::min())
            throw std::runtime_error("Integer overflow normalizing rational: " + j.dump());
        num = -num;
        den = -den;
    } else if (den == 0) {
        throw std::runtime_error("Zero denominator in rational: " + j.dump());
    }
    return {num, den};
}

// Agda emits signal values as int or {"numerator": n, "denominator": d}.
// Returns Rational for exact precision (no double truncation).
// Throws on unrecognized formats; callers catch at the public API boundary.
static auto parse_signal_value(const Json& j) -> Rational {
    if (j.is_number_integer())
        return Rational{j.get<std::int64_t>(), 1};
    if (j.is_number())
        return Rational::from_double(j.get<double>());
    if (j.is_object() && j.contains("numerator") && j.contains("denominator")) {
        auto [num, den] = parse_rational_dict(j);
        return Rational{num, den};
    }
    throw std::runtime_error("Expected number or {numerator, denominator}, got: " + j.dump());
}

// String → IssueCode lookup table.  Same shape as `error_code_table` at the
// top of this file; linear scan is fine on the cold validation path.
using IssueCodeEntry = std::pair<std::string_view, IssueCode>;
constexpr std::array<IssueCodeEntry, 21> issue_code_table{{
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
}};

static auto parse_issue_code(std::string_view s) -> IssueCode {
    for (const auto& [name, code] : issue_code_table)
        if (name == s)
            return code;
    return IssueCode::Unknown;
}

// Parse a JSON value as an exact Rational (for DBC signal parameters).
// Accepts plain integers or {numerator, denominator} dicts.
static auto parse_rational(const Json& j) -> Rational {
    if (j.is_number_integer())
        return Rational{j.get<std::int64_t>(), 1};
    if (j.is_object() && j.contains("numerator") && j.contains("denominator")) {
        auto [num, den] = parse_rational_dict(j);
        return Rational{num, den};
    }
    throw std::runtime_error("Expected integer or {numerator, denominator}, got: " + j.dump());
}

static auto parse_rational_as_int(const Json& j) -> std::int64_t {
    if (j.is_number_integer())
        return j.get<std::int64_t>();
    if (j.is_object() && j.contains("numerator") && j.contains("denominator")) {
        // parse_rational_dict normalizes den > 0, so the asymmetric INT64_MIN/-1
        // overflow check from the pre-extraction code is subsumed by the helper's
        // general (den<0, num==INT64_MIN) check.  After normalization num/den is safe.
        auto [num, den] = parse_rational_dict(j);
        if (num % den != 0)
            throw std::runtime_error("Non-exact rational in integer field: " + j.dump());
        return num / den;
    }
    throw std::runtime_error("Expected integer or {numerator, denominator}, got: " + j.dump());
}

// ---------------------------------------------------------------------------
// DBC parsing (for formatDBC response)
// ---------------------------------------------------------------------------

static auto parse_signal_def(const Json& j) -> DbcSignal {
    auto bo_str = j.value("byteOrder", "little_endian");
    ByteOrder bo{};
    if (bo_str == "little_endian")
        bo = ByteOrder::LittleEndian;
    else if (bo_str == "big_endian")
        bo = ByteOrder::BigEndian;
    else
        throw std::runtime_error("Unrecognized byteOrder: " + bo_str);

    SignalPresence presence = AlwaysPresent{};
    if (j.contains("multiplexor")) {
        const auto& arr = j.at("multiplex_values");
        std::vector<MultiplexValue> vals;
        vals.reserve(arr.size());
        for (const auto& elem : arr)
            vals.emplace_back(elem.get<std::uint32_t>());
        presence = Multiplexed{.multiplexor = SignalName{j.at("multiplexor").get<std::string>()},
                               .multiplex_values = std::move(vals)};
    }

    std::vector<std::string> receivers;
    if (j.contains("receivers")) {
        const auto& arr = j.at("receivers");
        receivers.reserve(arr.size());
        for (const auto& elem : arr)
            receivers.emplace_back(elem.get<std::string>());
    }

    std::vector<DbcValueEntry> value_descriptions;
    if (j.contains("valueDescriptions")) {
        const auto& arr = j.at("valueDescriptions");
        value_descriptions.reserve(arr.size());
        for (const auto& elem : arr)
            value_descriptions.push_back(DbcValueEntry{
                .value = elem.at("value").get<std::int64_t>(),
                .description = elem.at("description").get<std::string>(),
            });
    }

    return DbcSignal{
        .name = SignalName{j.at("name").get<std::string>()},
        .start_bit = BitPosition{j.at("startBit").get<std::uint16_t>()},
        .bit_length = BitLength{j.at("length").get<std::uint8_t>()},
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
    auto id_val = j.at("id").get<std::uint32_t>();
    const bool extended = j.value("extended", false);
    const CanId id = json_to_can_id(id_val, extended);

    auto dlc_result = bytes_to_dlc(j.at("dlc").get<std::size_t>());
    if (!dlc_result)
        throw std::runtime_error("Invalid DLC: " + dlc_result.error());

    std::vector<DbcSignal> signals;
    for (const auto& s : j.at("signals"))
        signals.push_back(parse_signal_def(s));

    std::vector<std::string> senders;
    if (j.contains("senders")) {
        const auto& arr = j.at("senders");
        senders.reserve(arr.size());
        for (const auto& elem : arr)
            senders.emplace_back(elem.get<std::string>());
    }

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
    for (const auto& s : j.at("signals"))
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
    auto name = j.at("name").get<std::string>();
    const auto raw_type = j.at("varType").get<int>();
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
    for (const auto& e : j.at("entries"))
        entries.push_back(DbcValueEntry{
            .value = e.at("value").get<std::int64_t>(),
            .description = e.at("description").get<std::string>(),
        });
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
    return DbcNode{.name = j.at("name").get<std::string>()};
}

static auto parse_can_id_fields(const Json& j, std::uint32_t& id, bool& extended) -> void {
    id = j.at("id").get<std::uint32_t>();
    extended = j.value("extended", false);
}

static auto parse_comment_target(const Json& j) -> DbcCommentTarget {
    const auto kind = j.at("kind").get<std::string>();
    if (kind == "network")
        return DbcCommentTargetNetwork{};
    if (kind == "node")
        return DbcCommentTargetNode{.node = j.at("node").get<std::string>()};
    if (kind == "message") {
        DbcCommentTargetMessage v;
        parse_can_id_fields(j, v.id, v.extended);
        return v;
    }
    if (kind == "signal") {
        DbcCommentTargetSignal v;
        parse_can_id_fields(j, v.id, v.extended);
        v.signal = j.at("signal").get<std::string>();
        return v;
    }
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
constexpr std::array<AttrScopeEntry, 7> attr_scope_table{{
    {"network", DbcAttrScope::Network},
    {"node", DbcAttrScope::Node},
    {"message", DbcAttrScope::Message},
    {"signal", DbcAttrScope::Signal},
    {"envVar", DbcAttrScope::EnvVar},
    {"nodeMsg", DbcAttrScope::NodeMsg},
    {"nodeSig", DbcAttrScope::NodeSig},
}};

static auto parse_attr_scope(std::string_view s) -> DbcAttrScope {
    for (const auto& [name, scope] : attr_scope_table)
        if (name == s)
            return scope;
    throw std::runtime_error("Unknown attribute scope: " + std::string{s});
}

static auto parse_attr_type(const Json& j) -> DbcAttrType {
    const auto kind = j.at("kind").get<std::string>();
    if (kind == "int")
        return DbcAttrTypeInt{.min = j.at("min").get<std::int64_t>(),
                              .max = j.at("max").get<std::int64_t>()};
    if (kind == "float")
        return DbcAttrTypeFloat{.min = parse_rational(j.at("min")),
                                .max = parse_rational(j.at("max"))};
    if (kind == "string")
        return DbcAttrTypeString{};
    if (kind == "enum") {
        std::vector<std::string> values;
        for (const auto& v : j.at("values"))
            values.push_back(v.get<std::string>());
        return DbcAttrTypeEnum{.values = std::move(values)};
    }
    if (kind == "hex")
        return DbcAttrTypeHex{.min = j.at("min").get<std::int64_t>(),
                              .max = j.at("max").get<std::int64_t>()};
    throw std::runtime_error("Unknown attribute type kind: " + kind);
}

static auto parse_attr_value(const Json& j) -> DbcAttrValue {
    const auto kind = j.at("kind").get<std::string>();
    if (kind == "int")
        return DbcAttrValueInt{.value = j.at("value").get<std::int64_t>()};
    if (kind == "float")
        return DbcAttrValueFloat{.value = parse_rational(j.at("value"))};
    if (kind == "string")
        return DbcAttrValueString{.value = j.at("value").get<std::string>()};
    if (kind == "enum")
        return DbcAttrValueEnum{.value = j.at("value").get<std::int64_t>()};
    if (kind == "hex")
        return DbcAttrValueHex{.value = j.at("value").get<std::int64_t>()};
    throw std::runtime_error("Unknown attribute value kind: " + kind);
}

static auto parse_attr_target(const Json& j) -> DbcAttrTarget {
    const auto kind = j.at("kind").get<std::string>();
    if (kind == "network")
        return DbcAttrTargetNetwork{};
    if (kind == "node")
        return DbcAttrTargetNode{.node = j.at("node").get<std::string>()};
    if (kind == "message") {
        DbcAttrTargetMessage v;
        parse_can_id_fields(j, v.id, v.extended);
        return v;
    }
    if (kind == "signal") {
        DbcAttrTargetSignal v;
        parse_can_id_fields(j, v.id, v.extended);
        v.signal = j.at("signal").get<std::string>();
        return v;
    }
    if (kind == "envVar")
        return DbcAttrTargetEnvVar{.env_var = j.at("envVar").get<std::string>()};
    if (kind == "nodeMsg") {
        DbcAttrTargetNodeMsg v;
        v.node = j.at("node").get<std::string>();
        parse_can_id_fields(j, v.id, v.extended);
        return v;
    }
    if (kind == "nodeSig") {
        DbcAttrTargetNodeSig v;
        v.node = j.at("node").get<std::string>();
        parse_can_id_fields(j, v.id, v.extended);
        v.signal = j.at("signal").get<std::string>();
        return v;
    }
    throw std::runtime_error("Unknown attribute target kind: " + kind);
}

static auto parse_attribute(const Json& j) -> DbcAttribute {
    const auto kind = j.at("kind").get<std::string>();
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

// Track E.8 (Plan B): inverse of json_serialize.cpp's raw_value_desc_to_json.
// Reads one unresolved RawValueDesc from the wire — message-id pair (id +
// optional extended) plus signalName + entries array. Wire shape is fixed
// at the cross-binding boundary, mirrored by Python `_normalize_raw_value_desc`
// and Go `parseUnresolvedValueDescs`.
static auto parse_raw_value_desc(const Json& j) -> DbcRawValueDesc {
    auto id_val = j.at("id").get<std::uint32_t>();
    const bool extended = j.value("extended", false);
    const CanId can_id = json_to_can_id(id_val, extended);
    std::vector<DbcValueEntry> entries;
    for (const auto& e : j.at("entries"))
        entries.push_back(DbcValueEntry{
            .value = e.at("value").get<std::int64_t>(),
            .description = e.at("description").get<std::string>(),
        });
    return DbcRawValueDesc{
        .can_id = can_id,
        .signal_name = j.at("signalName").get<std::string>(),
        .entries = std::move(entries),
    };
}

static auto parse_dbc_definition(const Json& j) -> DbcDefinition {
    std::vector<DbcMessage> messages;
    for (const auto& m : j.at("messages"))
        messages.push_back(parse_message_def(m));
    // Tier 1/2 metadata fields are optional on the wire — absent or empty
    // arrays both map to empty vectors here.
    std::vector<DbcSignalGroup> signal_groups;
    if (j.contains("signalGroups"))
        for (const auto& g : j.at("signalGroups"))
            signal_groups.push_back(parse_signal_group(g));
    std::vector<DbcEnvironmentVar> environment_vars;
    if (j.contains("environmentVars"))
        for (const auto& ev : j.at("environmentVars"))
            environment_vars.push_back(parse_env_var(ev));
    std::vector<DbcValueTable> value_tables;
    if (j.contains("valueTables"))
        for (const auto& vt : j.at("valueTables"))
            value_tables.push_back(parse_value_table(vt));
    std::vector<DbcNode> nodes;
    if (j.contains("nodes"))
        for (const auto& n : j.at("nodes"))
            nodes.push_back(parse_node(n));
    std::vector<DbcComment> comments;
    if (j.contains("comments"))
        for (const auto& c : j.at("comments"))
            comments.push_back(parse_comment(c));
    std::vector<DbcAttribute> attributes;
    if (j.contains("attributes"))
        for (const auto& a : j.at("attributes"))
            attributes.push_back(parse_attribute(a));
    std::vector<DbcRawValueDesc> unresolved_value_descriptions;
    if (j.contains("unresolvedValueDescs"))
        for (const auto& rvd : j.at("unresolvedValueDescs"))
            unresolved_value_descriptions.push_back(parse_raw_value_desc(rvd));
    return DbcDefinition{
        .version = j.value("version", ""),
        .messages = std::move(messages),
        .signal_groups = std::move(signal_groups),
        .environment_vars = std::move(environment_vars),
        .value_tables = std::move(value_tables),
        .nodes = std::move(nodes),
        .comments = std::move(comments),
        .attributes = std::move(attributes),
        .unresolved_value_descriptions = std::move(unresolved_value_descriptions),
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
        auto j = parse_bounded(input);
        auto status = j.value("status", "");
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
        auto j = parse_bounded(input);
        auto status = j.value("status", "");
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
        auto status = j.value("status", "");
        if (status == "error")
            return std::unexpected(make_json_error(ErrorKind::Validation, j));
        if (status != "validation")
            return std::unexpected(make_error(ErrorKind::Protocol, "Expected validation response"));

        std::vector<ValidationIssue> issues;
        for (const auto& issue : j.at("issues")) {
            auto sev_str = issue.value("severity", "");
            IssueSeverity severity{};
            if (sev_str == "error") {
                severity = IssueSeverity::Error;
            } else if (sev_str == "warning") {
                severity = IssueSeverity::Warning;
            } else {
                return std::unexpected(
                    make_error(ErrorKind::Protocol, "Unknown validation severity: " + sev_str));
            }
            issues.push_back({
                .severity = severity,
                .code = parse_issue_code(issue.value("code", "")),
                .detail = issue.value("detail", ""),
            });
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
        auto j = parse_bounded(input);
        auto status = j.value("status", "");
        if (status == "error")
            return std::unexpected(make_json_error(ErrorKind::Protocol, j));
        if (status != "success")
            return std::unexpected(
                make_error(ErrorKind::Protocol, "Unexpected extraction status: " + status));

        std::vector<SignalValue> values;
        for (const auto& v : j.value("values", Json::array()))
            values.push_back({SignalName{v.at("name").get<std::string>()},
                              PhysicalValue{parse_signal_value(v.at("value"))}});

        std::vector<std::pair<SignalName, std::string>> errors;
        for (const auto& e : j.value("errors", Json::array()))
            errors.emplace_back(SignalName{e.at("name").get<std::string>()}, e.value("error", ""));

        std::vector<SignalName> absent;
        for (const auto& a : j.value("absent", Json::array()))
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
        auto status = j.value("status", "");
        if (status == "error")
            return std::unexpected(make_json_error(ErrorKind::Protocol, j));
        if (status != "success")
            return std::unexpected(
                make_error(ErrorKind::Protocol, "Unexpected frame data status: " + status));

        const auto& data = j.at("data");
        FramePayload payload;
        payload.reserve(data.size());
        for (const auto& byte_val : data)
            payload.push_back(static_cast<std::byte>(byte_val.get<std::uint8_t>()));
        return payload;
    } catch (const std::exception& e) {
        return std::unexpected(make_error(ErrorKind::Protocol, e.what()));
    }
}

// Parse one inner per-property verdict object — shared between the
// streaming PropertyBatch path (frame response) and the EndStream
// StreamResult path (parse_stream_result).  R23 — AGDA-D-12.1.
static auto parse_property_result_entry(const Json& r) -> PropertyResult {
    auto entry_status = r.value("status", "");
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
    // Fast path: byte-level check for the common ack response.
    // Avoids full JSON parsing for ~99% of streaming frames.
    static constexpr std::string_view ack_compact = R"({"status":"ack"})";
    static constexpr std::string_view ack_spaced = R"({"status": "ack"})";
    if (input == ack_compact || input == ack_spaced)
        return FrameResponse{Ack{}};

    try {
        auto j = parse_bounded(input);
        auto status = j.value("status", "");

        if (status == "ack")
            return FrameResponse{Ack{}};

        if (status == "error")
            return std::unexpected(make_json_error(ErrorKind::Protocol, j));

        // R23 — AGDA-D-12.1: streaming PropertyResponse is now a
        // batch envelope `{"type": "property_batch", "results": [...]}`.
        // Each results entry is a PropertyResult (holds/fails/unresolved);
        // violations close the batch in source-order per the Agda
        // dispatchIterResult invariant.
        if (j.value("type", "") == "property_batch") {
            const auto& raw_results = j.at("results");
            if (!raw_results.is_array() || raw_results.empty())
                throw std::runtime_error(
                    "property_batch response 'results' must be a non-empty array "
                    "(zero-event frames are encoded as ack)");
            std::vector<PropertyResult> results;
            results.reserve(raw_results.size());
            for (const auto& r : raw_results)
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

// Parse one entry in the `warnings` array.  Extracted from
// `parse_stream_result` so the outer function stays under clang-tidy's
// readability-function-cognitive-complexity threshold (25).  R23 cluster C
// added the `contains("property_index")` guard, which bumped the outer
// function above the threshold.
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
        auto status = j.value("status", "");

        if (status == "error")
            return std::unexpected(make_json_error(ErrorKind::Protocol, j));
        if (status != "complete")
            return std::unexpected(make_error(ErrorKind::Protocol, "Expected complete response"));

        std::vector<PropertyResult> results;
        for (const auto& r : j.at("results"))
            results.push_back(parse_property_result_entry(r));

        std::vector<StreamWarning> warnings;
        if (j.contains("warnings")) {
            for (const auto& w : j.at("warnings"))
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
        auto status = j.value("status", "");
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
        auto status = j.value("status", "");
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
            for (const auto& issue : j.at("warnings")) {
                auto sev_str = issue.value("severity", "");
                IssueSeverity severity{};
                if (sev_str == "error") {
                    severity = IssueSeverity::Error;
                } else if (sev_str == "warning") {
                    severity = IssueSeverity::Warning;
                } else {
                    return std::unexpected(
                        make_error(ErrorKind::Protocol, "Unknown validation severity: " + sev_str));
                }
                warnings.push_back({
                    .severity = severity,
                    .code = parse_issue_code(issue.value("code", "")),
                    .detail = issue.value("detail", ""),
                });
            }
        }
        return ParsedDBC{.dbc = std::move(dbc), .warnings = std::move(warnings)};
    } catch (const std::exception& e) {
        return std::unexpected(make_error(ErrorKind::Protocol, e.what()));
    }
}

auto parse_dbc_text_response(std::string_view input) -> Result<std::string> {
    try {
        auto j = parse_bounded(input);
        auto status = j.value("status", "");
        if (status == "error")
            return std::unexpected(make_json_error(ErrorKind::Protocol, j));
        if (status != "success")
            return std::unexpected(make_error(
                ErrorKind::Protocol, "Unexpected formatDBCText response status: " + status));
        if (!j.contains("text") || !j.at("text").is_string())
            return std::unexpected(
                make_error(ErrorKind::Protocol,
                           "Missing or non-string 'text' field in formatDBCText response"));
        return j.at("text").get<std::string>();
    } catch (const std::exception& e) {
        return std::unexpected(make_error(ErrorKind::Protocol, e.what()));
    }
}

} // namespace aletheia::detail
