// SPDX-License-Identifier: BSD-2-Clause
// JSON parsing: Agda core response strings → C++ types.
#include "detail/json.hpp"

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
// for the 51-entry table on a cold parse path.
using ErrorCodeEntry = std::pair<std::string_view, ErrorCode>;
constexpr std::array<ErrorCodeEntry, 51> error_code_table{{
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
    // Frame errors
    {"frame_signal_not_found", ErrorCode::FrameSignalNotFound},
    {"frame_signal_index_oob", ErrorCode::FrameSignalIndexOob},
    {"frame_injection_failed", ErrorCode::FrameInjectionFailed},
    {"frame_signals_overlap", ErrorCode::FrameSignalsOverlap},
    {"frame_can_id_not_found", ErrorCode::FrameCanIdNotFound},
    {"frame_can_id_mismatch", ErrorCode::FrameCanIdMismatch},
    {"frame_signal_value_out_of_bounds", ErrorCode::FrameSignalValueOutOfBounds},
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
    return make_error(kind, j.at("message").get<std::string>(), code);
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
        auto num = j.at("numerator").get<std::int64_t>();
        auto den = j.at("denominator").get<std::int64_t>();
        if (den == 0)
            throw std::runtime_error("Zero denominator in rational: " + j.dump());
        if (den < 0) {
            if (num == std::numeric_limits<std::int64_t>::min())
                throw std::runtime_error("Integer overflow normalizing rational: " + j.dump());
            num = -num;
            den = -den;
        }
        return Rational{num, den};
    }
    throw std::runtime_error("Expected number or {numerator, denominator}, got: " + j.dump());
}

static auto parse_issue_code(const std::string& code) -> IssueCode {
    if (code == "duplicate_message_id")
        return IssueCode::DuplicateMessageId;
    if (code == "duplicate_message_name")
        return IssueCode::DuplicateMessageName;
    if (code == "duplicate_signal_name")
        return IssueCode::DuplicateSignalName;
    if (code == "factor_zero")
        return IssueCode::FactorZero;
    if (code == "multiplexor_not_found")
        return IssueCode::MultiplexorNotFound;
    if (code == "multiplexor_cycle")
        return IssueCode::MultiplexorCycle;
    if (code == "global_name_collision")
        return IssueCode::GlobalNameCollision;
    if (code == "min_exceeds_max")
        return IssueCode::MinExceedsMax;
    if (code == "signal_exceeds_dlc")
        return IssueCode::SignalExceedsDlc;
    if (code == "signal_overlap")
        return IssueCode::SignalOverlap;
    if (code == "bit_length_zero")
        return IssueCode::BitLengthZero;
    if (code == "offset_scale_range")
        return IssueCode::OffsetScaleRange;
    if (code == "empty_message")
        return IssueCode::EmptyMessage;
    if (code == "start_bit_out_of_range")
        return IssueCode::StartBitOutOfRange;
    if (code == "bit_length_excessive")
        return IssueCode::BitLengthExcessive;
    if (code == "multiplexor_non_unit_scaling")
        return IssueCode::MultiplexorNonUnitScaling;
    if (code == "duplicate_attribute_name")
        return IssueCode::DuplicateAttributeName;
    if (code == "unknown_comment_target")
        return IssueCode::UnknownCommentTarget;
    if (code == "unknown_message_sender")
        return IssueCode::UnknownMessageSender;
    return IssueCode::Unknown;
}

// Parse a JSON value as an exact Rational (for DBC signal parameters).
// Accepts plain integers or {numerator, denominator} dicts.
static auto parse_rational(const Json& j) -> Rational {
    if (j.is_number_integer())
        return Rational{j.get<std::int64_t>(), 1};
    if (j.is_object() && j.contains("numerator") && j.contains("denominator")) {
        auto num = j.at("numerator").get<std::int64_t>();
        auto den = j.at("denominator").get<std::int64_t>();
        if (den == 0)
            throw std::runtime_error("Zero denominator in rational: " + j.dump());
        // Normalize: denominator always positive
        if (den < 0) {
            if (num == std::numeric_limits<std::int64_t>::min())
                throw std::runtime_error("Integer overflow normalizing rational: " + j.dump());
            num = -num;
            den = -den;
        }
        return Rational{num, den};
    }
    throw std::runtime_error("Expected integer or {numerator, denominator}, got: " + j.dump());
}

static auto parse_rational_as_int(const Json& j) -> std::int64_t {
    if (j.is_number_integer())
        return j.get<std::int64_t>();
    if (j.is_object() && j.contains("numerator") && j.contains("denominator")) {
        auto num = j.at("numerator").get<std::int64_t>();
        auto den = j.at("denominator").get<std::int64_t>();
        if (den == 0)
            throw std::runtime_error("Zero denominator in rational: " + j.dump());
        if (den == -1 && num == std::numeric_limits<std::int64_t>::min())
            throw std::runtime_error("Integer overflow in rational: " + j.dump());
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
                               .mux_values = std::move(vals)};
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
    };
}

static auto parse_message_def(const Json& j) -> DbcMessage {
    auto id_val = j.at("id").get<std::uint32_t>();
    const bool extended = j.value("extended", false);

    const CanId id = [&]() -> CanId {
        if (extended) {
            auto result = ExtendedId::create(id_val);
            if (!result)
                throw std::runtime_error("Invalid extended CAN ID " + std::to_string(id_val) +
                                         ": " + result.error());
            return CanId{*result};
        }
        if (id_val > std::numeric_limits<std::uint16_t>::max())
            throw std::runtime_error("Standard CAN ID value " + std::to_string(id_val) +
                                     " exceeds uint16 range");
        auto result = StandardId::create(static_cast<std::uint16_t>(id_val));
        if (!result)
            throw std::runtime_error("Invalid standard CAN ID " + std::to_string(id_val) + ": " +
                                     result.error());
        return CanId{*result};
    }();

    auto dlc_result = bytes_to_dlc(j.at("dlc").get<std::size_t>());
    if (!dlc_result)
        throw std::runtime_error("Invalid DLC: " + dlc_result.error());

    std::vector<DbcSignal> signals;
    for (const auto& s : j.at("signals"))
        signals.push_back(parse_signal_def(s));

    return DbcMessage{
        .id = id,
        .name = MessageName{j.at("name").get<std::string>()},
        .dlc = *dlc_result,
        .sender = NodeName{j.value("sender", "")},
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

static auto parse_attr_scope(const std::string& s) -> DbcAttrScope {
    if (s == "network")
        return DbcAttrScope::Network;
    if (s == "node")
        return DbcAttrScope::Node;
    if (s == "message")
        return DbcAttrScope::Message;
    if (s == "signal")
        return DbcAttrScope::Signal;
    if (s == "envVar")
        return DbcAttrScope::EnvVar;
    if (s == "nodeMsg")
        return DbcAttrScope::NodeMsg;
    if (s == "nodeSig")
        return DbcAttrScope::NodeSig;
    throw std::runtime_error("Unknown attribute scope: " + s);
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
    return DbcDefinition{
        .version = j.value("version", ""),
        .messages = std::move(messages),
        .signal_groups = std::move(signal_groups),
        .environment_vars = std::move(environment_vars),
        .value_tables = std::move(value_tables),
        .nodes = std::move(nodes),
        .comments = std::move(comments),
        .attributes = std::move(attributes),
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
        auto j = Json::parse(input);
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
        auto j = Json::parse(input);
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
        auto j = Json::parse(input);
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
        auto j = Json::parse(input);
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
        auto j = Json::parse(input);
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

auto parse_frame_response(std::string_view input) -> Result<FrameResponse> {
    // Fast path: byte-level check for the common ack response.
    // Avoids full JSON parsing for ~99% of streaming frames.
    static constexpr std::string_view ack_compact = R"({"status":"ack"})";
    static constexpr std::string_view ack_spaced = R"({"status": "ack"})";
    if (input == ack_compact || input == ack_spaced)
        return FrameResponse{Ack{}};

    try {
        auto j = Json::parse(input);
        auto status = j.value("status", "");

        if (status == "ack")
            return FrameResponse{Ack{}};

        if (status == "fails") {
            if (j.value("type", "") != "property")
                throw std::runtime_error("Expected type \"property\" in violation response");
            auto idx = parse_rational_as_int(j.at("property_index"));
            if (idx < 0)
                throw std::runtime_error("Negative property_index: " + std::to_string(idx));
            auto ts = parse_rational_as_int(j.at("timestamp"));
            if (ts < 0)
                throw std::runtime_error("Negative timestamp: " + std::to_string(ts));
            std::string reason;
            if (j.contains("reason") && j.at("reason").is_string())
                reason = j.at("reason").get<std::string>();
            return FrameResponse{Violation{
                .property_index = PropertyIndex{static_cast<std::size_t>(idx)},
                .timestamp = Timestamp{ts},
                .reason = std::move(reason),
            }};
        }

        if (status == "error")
            return std::unexpected(make_json_error(ErrorKind::Protocol, j));

        return std::unexpected(
            make_error(ErrorKind::Protocol, "Unexpected frame status: " + status));
    } catch (const std::exception& e) {
        return std::unexpected(make_error(ErrorKind::Protocol, e.what()));
    }
}

auto parse_stream_result(std::string_view input) -> Result<StreamResult> {
    try {
        auto j = Json::parse(input);
        auto status = j.value("status", "");

        if (status == "error")
            return std::unexpected(make_json_error(ErrorKind::Protocol, j));
        if (status != "complete")
            return std::unexpected(make_error(ErrorKind::Protocol, "Expected complete response"));

        std::vector<PropertyResult> results;
        for (const auto& r : j.at("results")) {
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

            results.push_back({
                .property_index = PropertyIndex{static_cast<std::size_t>(idx)},
                .verdict = verdict,
                .timestamp = ts,
                .reason = std::move(reason),
            });
        }
        return StreamResult{.results = std::move(results)};
    } catch (const std::exception& e) {
        return std::unexpected(make_error(ErrorKind::Protocol, e.what()));
    }
}

auto parse_dbc_response(std::string_view input) -> Result<DbcDefinition> {
    try {
        auto j = Json::parse(input);
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

} // namespace aletheia::detail
