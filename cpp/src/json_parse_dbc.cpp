// SPDX-FileCopyrightText: 2025 Nicolas Pelletier
// SPDX-License-Identifier: BSD-2-Clause
// JSON parsing of a DBC definition: the signal, message and metadata decoders
// behind the formatDBC and parsed-DBC responses.
//
// The DBC a reply carries sits at "dbc", and every refusal below names its
// place from there: a signal's field is at "dbc/messages/signals/<key>". Every
// key the kernel writes is required, and each number or string is read by kind
// only, its range the kernel's, decided when it read the DBC and proven of every
// reply. A signal's byte order and presence, a comment target's kind, an
// attribute's kind and the kinds of its value and its target, a definition's
// scope and its type's kind are read by field_member and field_word, which
// refuse a word outside the place's words. The keys of an object are read in
// the order the other bindings read them, so a reply broken at two places is
// refused at the same one by all four.
#include "detail/json_parse_helpers.hpp"
#include "detail/kernel_value.hpp"
#include "detail/reply_shape.hpp"
#include "detail/wide_json.hpp"

#include <aletheia/dbc.hpp>
#include <aletheia/types.hpp>

#include <array>
#include <cstddef>
#include <cstdint>
#include <string>
#include <string_view>
#include <utility>
#include <vector>

namespace aletheia::detail {

// The identifier of the object at `path`: its "extended" flag, then "id" at
// the width the flag names, whose range the kernel proves.
static auto read_can_id(Json const& m, ReplyPath const& path) -> CanId {
    if (field_bool(m, path, "extended"))
        return KernelValue::extended_id(field_unsigned<std::uint32_t>(m, path, "id"));
    return KernelValue::standard_id(field_unsigned<std::uint16_t>(m, path, "id"));
}

// A message's length code, read from the byte count the reply writes; a count
// no code stands for, which the kernel never writes, is refused as the number
// the place does not hold.
static auto read_dlc(Json const& m, ReplyPath const& path) -> Dlc {
    auto const dlc = bytes_to_dlc(field_unsigned<std::size_t>(m, path, "dlc"));
    if (!dlc)
        throw reply_refusal(path.at("dlc"), expect_number, came(m, "dlc"));
    return dlc.value();
}

// The presence the kernel states for every signal, "always" or "multiplexed",
// a multiplexed signal's multiplexor a string and its selector values whole
// numbers.
static auto read_presence(Json const& j, ReplyPath const& path) -> SignalPresence {
    auto const presence = field_word(j, path, "presence", {"always", "multiplexed"});
    if (presence == "always")
        return AlwaysPresent{};
    auto multiplexor = field_string(j, path, "multiplexor");
    auto const place = path.at("multiplex_values");
    std::vector<MultiplexValue> values;
    for (auto const& value : field_array(j, path, "multiplex_values"))
        values.emplace_back(read_uint128(value, place));
    return Multiplexed{.multiplexor = SignalName{std::move(multiplexor)},
                       .multiplex_values = std::move(values)};
}

// One value description, the shape of an inline VAL_ entry and of a
// VAL_TABLE_ row: a signed key and its text.
static auto read_value_entry(Json const& e, ReplyPath const& path) -> DbcValueEntry {
    return DbcValueEntry{
        .value = field_sign_magnitude(e, path, "value"),
        .description = field_string(e, path, "description"),
    };
}

// The byte orders the kernel writes.
constexpr auto byte_order_table = std::to_array<std::pair<std::string_view, ByteOrder>>({
    {"little_endian", ByteOrder::LittleEndian},
    {"big_endian", ByteOrder::BigEndian},
});

static auto read_signal(Json const& j, ReplyPath const& path) -> DbcSignal {
    auto name = field_string(j, path, "name");
    auto const start_bit = field_unsigned<std::uint16_t>(j, path, "startBit");
    auto const length = field_unsigned<std::uint16_t>(j, path, "length");
    auto const byte_order = field_member(j, path, "byteOrder", byte_order_table);
    auto const is_signed = field_bool(j, path, "signed");
    auto const factor = field_rational(j, path, "factor");
    auto const offset = field_rational(j, path, "offset");
    auto const minimum = field_rational(j, path, "minimum");
    auto const maximum = field_rational(j, path, "maximum");
    auto unit = field_string(j, path, "unit");
    auto receivers = field_strings<NodeName>(j, path, "receivers");
    auto value_descriptions = field_objects(j, path, "valueDescriptions", read_value_entry);
    auto presence = read_presence(j, path);
    return DbcSignal{
        .name = SignalName{std::move(name)},
        .start_bit = BitPosition{start_bit},
        .bit_length = BitLength{length},
        .byte_order = byte_order,
        .is_signed = is_signed,
        .factor = RationalFactor{factor},
        .offset = RationalOffset{offset},
        .minimum = RationalBound{minimum},
        .maximum = RationalBound{maximum},
        .unit = Unit{std::move(unit)},
        .presence = std::move(presence),
        .receivers = std::move(receivers),
        .value_descriptions = std::move(value_descriptions),
    };
}

static auto read_message(Json const& j, ReplyPath const& path) -> DbcMessage {
    auto signals = field_objects(j, path, "signals", read_signal);
    auto name = field_string(j, path, "name");
    auto const id = read_can_id(j, path);
    auto const dlc = read_dlc(j, path);
    auto sender = field_string(j, path, "sender");
    auto senders = field_strings<NodeName>(j, path, "senders");
    return DbcMessage{
        .id = id,
        .name = MessageName{std::move(name)},
        .dlc = dlc,
        .sender = NodeName{std::move(sender)},
        .senders = std::move(senders),
        .signals = std::move(signals),
    };
}

static auto read_signal_group(Json const& g, ReplyPath const& path) -> DbcSignalGroup {
    return DbcSignalGroup{
        .name = field_string(g, path, "name"),
        .signals = field_strings<SignalName>(g, path, "signals"),
    };
}

// An environment variable's type from its tag, 2 for a string the last arm.
static auto var_type_of(std::uint64_t tag) -> DbcVarType {
    switch (tag) {
    case 0:
        return DbcVarType::Int;
    case 1:
        return DbcVarType::Float;
    default:
        return DbcVarType::String;
    }
}

static auto read_environment_var(Json const& ev, ReplyPath const& path) -> DbcEnvironmentVar {
    return DbcEnvironmentVar{
        .name = field_string(ev, path, "name"),
        .var_type = var_type_of(field_unsigned<std::uint64_t>(ev, path, "varType")),
        .initial = field_rational(ev, path, "initial"),
        .minimum = field_rational(ev, path, "minimum"),
        .maximum = field_rational(ev, path, "maximum"),
    };
}

static auto read_value_table(Json const& vt, ReplyPath const& path) -> DbcValueTable {
    return DbcValueTable{
        .name = field_string(vt, path, "name"),
        .entries = field_objects(vt, path, "entries", read_value_entry),
    };
}

// A value description the text parser could not attach to a signal, its CAN
// id read as a message's.
static auto read_raw_value_desc(Json const& rvd, ReplyPath const& path) -> DbcRawValueDesc {
    return DbcRawValueDesc{
        .can_id = read_can_id(rvd, path),
        .signal_name = field_string(rvd, path, "signalName"),
        .entries = field_objects(rvd, path, "entries", read_value_entry),
    };
}

// ---------------------------------------------------------------------------
// Tier 2 parsers (nodes / comments / attributes), each variant dispatched on
// its "kind".
// ---------------------------------------------------------------------------

static auto read_node(Json const& n, ReplyPath const& path) -> DbcNode {
    return DbcNode{.name = NodeName{field_string(n, path, "name")}};
}

// What a comment is attached to.
static auto read_comment_target(Json const& m, ReplyPath const& path) -> DbcCommentTarget {
    auto const kind =
        field_word(m, path, "kind", {"network", "node", "message", "signal", "envVar"});
    if (kind == "network")
        return DbcCommentTargetNetwork{};
    if (kind == "node")
        return DbcCommentTargetNode{.node = NodeName{field_string(m, path, "node")}};
    if (kind == "message")
        return DbcCommentTargetMessage{.id = read_can_id(m, path)};
    if (kind == "signal")
        return DbcCommentTargetSignal{.id = read_can_id(m, path),
                                      .signal = field_string(m, path, "signal")};
    return DbcCommentTargetEnvVar{.env_var = field_string(m, path, "envVar")};
}

static auto read_comment(Json const& c, ReplyPath const& path) -> DbcComment {
    return DbcComment{
        .target = field_object_of(c, path, "target", read_comment_target),
        .text = field_string(c, path, "text"),
    };
}

// The scopes the kernel writes.
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

// An attribute definition's type.
static auto read_attr_type(Json const& m, ReplyPath const& path) -> DbcAttrType {
    auto const kind = field_word(m, path, "kind", {"int", "float", "string", "enum", "hex"});
    if (kind == "int")
        return DbcAttrTypeInt{.min = field_int64(m, path, "min"),
                              .max = field_int64(m, path, "max")};
    if (kind == "float")
        return DbcAttrTypeFloat{.min = field_rational(m, path, "min"),
                                .max = field_rational(m, path, "max")};
    if (kind == "string")
        return DbcAttrTypeString{};
    if (kind == "enum")
        return DbcAttrTypeEnum{.values = field_strings<std::string>(m, path, "values")};
    return DbcAttrTypeHex{.min = field_int64(m, path, "min"), .max = field_int64(m, path, "max")};
}

// An attribute's value.
static auto read_attr_value(Json const& m, ReplyPath const& path) -> DbcAttrValue {
    auto const kind = field_word(m, path, "kind", {"int", "float", "string", "enum", "hex"});
    if (kind == "int")
        return DbcAttrValueInt{.value = field_int64(m, path, "value")};
    if (kind == "float")
        return DbcAttrValueFloat{.value = field_rational(m, path, "value")};
    if (kind == "string")
        return DbcAttrValueString{.value = field_string(m, path, "value")};
    if (kind == "enum")
        return DbcAttrValueEnum{.value = field_int64(m, path, "value")};
    return DbcAttrValueHex{.value = field_int64(m, path, "value")};
}

// What an attribute is assigned to; every kind but "network", "node" and
// "envVar" carries a CAN id, read before its other keys.
static auto read_attr_target(Json const& m, ReplyPath const& path) -> DbcAttrTarget {
    auto const kind = field_word(
        m, path, "kind", {"network", "node", "message", "signal", "envVar", "nodeMsg", "nodeSig"});
    if (kind == "network")
        return DbcAttrTargetNetwork{};
    if (kind == "node")
        return DbcAttrTargetNode{.node = NodeName{field_string(m, path, "node")}};
    if (kind == "envVar")
        return DbcAttrTargetEnvVar{.env_var = field_string(m, path, "envVar")};
    auto const id = read_can_id(m, path);
    if (kind == "message")
        return DbcAttrTargetMessage{.id = id};
    if (kind == "signal")
        return DbcAttrTargetSignal{.id = id, .signal = field_string(m, path, "signal")};
    auto node = NodeName{field_string(m, path, "node")};
    if (kind == "nodeMsg")
        return DbcAttrTargetNodeMsg{.node = std::move(node), .id = id};
    return DbcAttrTargetNodeSig{
        .node = std::move(node), .id = id, .signal = field_string(m, path, "signal")};
}

// One attribute entry.
static auto read_attribute(Json const& m, ReplyPath const& path) -> DbcAttribute {
    auto const kind = field_word(m, path, "kind", {"definition", "default", "assignment"});
    auto name = field_string(m, path, "name");
    if (kind == "definition")
        return DbcAttrDef{
            .name = std::move(name),
            .scope = field_member(m, path, "scope", attr_scope_table),
            .attr_type = field_object_of(m, path, "attrType", read_attr_type),
        };
    if (kind == "default")
        return DbcAttrDefault{
            .name = std::move(name),
            .value = field_object_of(m, path, "value", read_attr_value),
        };
    return DbcAttrAssign{
        .name = std::move(name),
        .target = field_object_of(m, path, "target", read_attr_target),
        .value = field_object_of(m, path, "value", read_attr_value),
    };
}

auto parse_dbc_definition(Json const& dbc) -> DbcDefinition {
    auto const path = ReplyPath{}.at("dbc");
    return DbcDefinition{
        .version = field_string(dbc, path, "version"),
        .messages = field_objects(dbc, path, "messages", read_message),
        .signal_groups = field_objects(dbc, path, "signalGroups", read_signal_group),
        .environment_vars = field_objects(dbc, path, "environmentVars", read_environment_var),
        .value_tables = field_objects(dbc, path, "valueTables", read_value_table),
        .nodes = field_objects(dbc, path, "nodes", read_node),
        .comments = field_objects(dbc, path, "comments", read_comment),
        .attributes = field_objects(dbc, path, "attributes", read_attribute),
        .unresolved_value_descs =
            field_objects(dbc, path, "unresolvedValueDescs", read_raw_value_desc),
    };
}

} // namespace aletheia::detail
