// SPDX-FileCopyrightText: 2025 Nicolas Pelletier
// SPDX-License-Identifier: BSD-2-Clause
// JSON parsing of a DBC definition: the signal, message and metadata decoders
// behind the formatDBC and parsed-DBC responses.
#include "detail/json_parse_helpers.hpp"

#include <aletheia/dbc.hpp>
#include <aletheia/detail/checked.hpp>
#include <aletheia/types.hpp>

#include <nlohmann/json.hpp>

#include <array>
#include <cstddef>
#include <cstdint>
#include <stdexcept>
#include <string>
#include <string_view>
#include <type_traits>
#include <utility>
#include <vector>

namespace aletheia::detail {

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
    constexpr auto byte_orders = std::to_array<std::pair<std::string_view, ByteOrder>>({
        {"little_endian", ByteOrder::LittleEndian},
        {"big_endian", ByteOrder::BigEndian},
    });
    auto const bo = lookup(byte_orders, bo_str);
    if (!bo)
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
        .byte_order = bo.value(),
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
        auto const result = ExtendedId::create(id_val);
        if (!result)
            throw std::runtime_error("Invalid extended CAN ID " + std::to_string(id_val) + ": " +
                                     std::string{detail::error_of(result).message()});
        return CanId{result.value()};
    }
    // The factory takes the 16 bits a standard id fits in and refuses past 11;
    // a wider value is refused here rather than truncated into its range.
    if (!std::in_range<std::uint16_t>(id_val))
        throw std::runtime_error("Standard CAN ID value " + std::to_string(id_val) +
                                 " exceeds 16 bits");
    auto const result = StandardId::create(static_cast<std::uint16_t>(id_val));
    if (!result)
        throw std::runtime_error("Invalid standard CAN ID " + std::to_string(id_val) + ": " +
                                 std::string{detail::error_of(result).message()});
    return CanId{result.value()};
}

static auto parse_message_def(const Json& j) -> DbcMessage {
    auto const id_val = require_uint<std::uint32_t>(j.at("id"), "message id");
    auto const extended = j.value("extended", false);
    auto const id = json_to_can_id(id_val, extended);

    auto const dlc_result = bytes_to_dlc(require_uint<std::size_t>(j.at("dlc"), "dlc"));
    if (!dlc_result)
        throw std::runtime_error("Invalid DLC: " +
                                 std::string{detail::error_of(dlc_result).message()});

    std::vector<DbcSignal> signals;
    for (auto const& s : j.at("signals"))
        signals.push_back(parse_signal_def(s));

    auto senders = parse_optional_array(
        j, "senders", [](const Json& elem) { return NodeName{elem.get<std::string>()}; });

    return DbcMessage{
        .id = id,
        .name = MessageName{j.at("name").get<std::string>()},
        .dlc = dlc_result.value(),
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
    if (auto const scope = lookup(attr_scope_table, s))
        return scope.value();
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
            v.get_to(values.emplace_back());
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
    auto const extended = j.value("extended", false);
    auto const can_id = json_to_can_id(id_val, extended);
    std::vector<DbcValueEntry> entries;
    for (auto const& e : j.at("entries"))
        entries.push_back(parse_value_entry(e, "value-description value"));
    return DbcRawValueDesc{
        .can_id = can_id,
        .signal_name = j.at("signalName").get<std::string>(),
        .entries = std::move(entries),
    };
}

auto parse_dbc_definition(const Json& j) -> DbcDefinition {
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

} // namespace aletheia::detail
