// SPDX-License-Identifier: BSD-2-Clause
// JSON serialization: C++ types → JSON command strings for the Agda core.
#include "detail/json.hpp"

#include <nlohmann/json.hpp>

#include <cstddef>
#include <cstdint>
#include <format>
#include <span>
#include <stdexcept>
#include <string>
#include <string_view>
#include <type_traits>
#include <utility>
#include <variant>

using Json = nlohmann::json;

namespace aletheia::detail {

// ---------------------------------------------------------------------------
// Helpers
// ---------------------------------------------------------------------------

static auto can_id_numeric(const CanId& id) -> std::uint32_t {
    return std::visit([](const auto& v) -> std::uint32_t { return v.value(); }, id);
}

static auto can_id_extended(const CanId& id) -> bool {
    return std::holds_alternative<ExtendedId>(id);
}

static auto rational_to_json(const Rational& r) -> Json {
    if (r.denominator == 1)
        return r.numerator;
    return {{"numerator", r.numerator}, {"denominator", r.denominator}};
}

static auto presence_to_json(const SignalPresence& p, Json& sig) -> void {
    // Mirror the Agda wire form: emit "presence": "always" explicitly for
    // AlwaysPresent signals; emit "multiplexor" + "multiplex_values" for
    // Multiplexed. Cross-binding parity: Python and Go both emit the
    // explicit "presence": "always", and parse_dbc_text returns it on the
    // wire. Agda's parser accepts the absence-of-multiplexor shorthand
    // too, but the explicit form is the canonical one (B.3.j).
    std::visit(
        [&sig](auto&& v) {
            using T = std::decay_t<decltype(v)>;
            if constexpr (std::is_same_v<T, AlwaysPresent>) {
                sig["presence"] = "always";
            } else if constexpr (std::is_same_v<T, Multiplexed>) {
                sig["multiplexor"] = v.multiplexor.get();
                auto arr = Json::array();
                for (const auto& mv : v.mux_values)
                    arr.push_back(mv.get());
                sig["multiplex_values"] = std::move(arr);
            } else {
                static_assert(sizeof(T) == 0, "Unhandled SignalPresence type");
            }
        },
        p);
}

static auto signal_def_to_json(const DbcSignal& s) -> Json {
    Json vds = Json::array();
    for (const auto& e : s.value_descriptions)
        vds.push_back(Json{{"value", e.value}, {"description", e.description}});
    Json sig = {
        {"name", s.name.get()},
        {"startBit", s.start_bit.get()},
        {"length", s.bit_length.get()},
        {"byteOrder", s.byte_order == ByteOrder::LittleEndian ? "little_endian" : "big_endian"},
        {"signed", s.is_signed},
        {"factor", rational_to_json(s.factor.get())},
        {"offset", rational_to_json(s.offset.get())},
        {"minimum", rational_to_json(s.minimum.get())},
        {"maximum", rational_to_json(s.maximum.get())},
        {"unit", s.unit.get()},
        {"receivers", s.receivers},
        {"valueDescriptions", std::move(vds)},
    };
    presence_to_json(s.presence, sig);
    return sig;
}

static auto message_to_json(const DbcMessage& m) -> Json {
    Json sigs = Json::array();
    for (const auto& s : m.signals)
        sigs.push_back(signal_def_to_json(s));
    Json msg = {
        {"id", can_id_numeric(m.id)}, {"name", m.name.get()}, {"dlc", dlc_to_bytes(m.dlc)},
        {"sender", m.sender.get()},   {"senders", m.senders}, {"signals", std::move(sigs)},
    };
    // Mirror the Agda wire form: emit "extended" only when the CAN ID is
    // extended (29-bit). Agda omits the field for standard 11-bit frames;
    // its parser accepts both forms but the omit-when-false shape is
    // canonical (matches attach_can_id used for comment / attribute targets,
    // and the same convention enforced by the Python and Go bindings — B.3.j).
    if (can_id_extended(m.id))
        msg["extended"] = true;
    return msg;
}

static auto signal_group_to_json(const DbcSignalGroup& g) -> Json {
    Json sigs = Json::array();
    for (const auto& sn : g.signals)
        sigs.push_back(sn.get());
    return {{"name", g.name}, {"signals", std::move(sigs)}};
}

static auto env_var_to_json(const DbcEnvironmentVar& ev) -> Json {
    return {
        {"name", ev.name},
        {"varType", static_cast<int>(ev.var_type)},
        {"initial", rational_to_json(ev.initial)},
        {"minimum", rational_to_json(ev.minimum)},
        {"maximum", rational_to_json(ev.maximum)},
    };
}

static auto value_table_to_json(const DbcValueTable& t) -> Json {
    Json entries = Json::array();
    for (const auto& e : t.entries)
        entries.push_back(Json{{"value", e.value}, {"description", e.description}});
    return {{"name", t.name}, {"entries", std::move(entries)}};
}

// ---------------------------------------------------------------------------
// Tier 2 serializers (nodes / comments / attributes). Wire format mirrors
// Agda's formatter in src/Aletheia/DBC/Formatter.agda — every tagged union
// carries "kind" as the first field, and extended-ID flags are emitted only
// when true to match formatCANId's omission on 11-bit IDs.
// ---------------------------------------------------------------------------

static auto node_to_json(const DbcNode& n) -> Json {
    return {{"name", n.name}};
}

static auto attach_can_id(Json& obj, std::uint32_t id, bool extended) -> void {
    obj["id"] = id;
    if (extended)
        obj["extended"] = true;
}

static auto comment_target_to_json(const DbcCommentTarget& t) -> Json {
    return std::visit(
        [](auto&& v) -> Json {
            using T = std::decay_t<decltype(v)>;
            if constexpr (std::is_same_v<T, DbcCommentTargetNetwork>)
                return {{"kind", "network"}};
            else if constexpr (std::is_same_v<T, DbcCommentTargetNode>)
                return {{"kind", "node"}, {"node", v.node}};
            else if constexpr (std::is_same_v<T, DbcCommentTargetMessage>) {
                Json out = {{"kind", "message"}};
                attach_can_id(out, v.id, v.extended);
                return out;
            } else if constexpr (std::is_same_v<T, DbcCommentTargetSignal>) {
                Json out = {{"kind", "signal"}};
                attach_can_id(out, v.id, v.extended);
                out["signal"] = v.signal;
                return out;
            } else if constexpr (std::is_same_v<T, DbcCommentTargetEnvVar>)
                return {{"kind", "envVar"}, {"envVar", v.env_var}};
            else
                static_assert(sizeof(T) == 0, "Unhandled DbcCommentTarget variant");
        },
        t);
}

static auto comment_to_json(const DbcComment& c) -> Json {
    return {{"target", comment_target_to_json(c.target)}, {"text", c.text}};
}

static auto attr_scope_to_json(DbcAttrScope s) -> std::string {
    switch (s) {
    case DbcAttrScope::Network:
        return "network";
    case DbcAttrScope::Node:
        return "node";
    case DbcAttrScope::Message:
        return "message";
    case DbcAttrScope::Signal:
        return "signal";
    case DbcAttrScope::EnvVar:
        return "envVar";
    case DbcAttrScope::NodeMsg:
        return "nodeMsg";
    case DbcAttrScope::NodeSig:
        return "nodeSig";
    }
    throw std::runtime_error("Invalid DbcAttrScope");
}

static auto attr_type_to_json(const DbcAttrType& t) -> Json {
    return std::visit(
        [](auto&& v) -> Json {
            using T = std::decay_t<decltype(v)>;
            if constexpr (std::is_same_v<T, DbcAttrTypeInt>)
                return {{"kind", "int"}, {"min", v.min}, {"max", v.max}};
            else if constexpr (std::is_same_v<T, DbcAttrTypeFloat>)
                return {{"kind", "float"},
                        {"min", rational_to_json(v.min)},
                        {"max", rational_to_json(v.max)}};
            else if constexpr (std::is_same_v<T, DbcAttrTypeString>)
                return {{"kind", "string"}};
            else if constexpr (std::is_same_v<T, DbcAttrTypeEnum>) {
                Json values = Json::array();
                for (const auto& s : v.values)
                    values.push_back(s);
                return {{"kind", "enum"}, {"values", std::move(values)}};
            } else if constexpr (std::is_same_v<T, DbcAttrTypeHex>)
                return {{"kind", "hex"}, {"min", v.min}, {"max", v.max}};
            else
                static_assert(sizeof(T) == 0, "Unhandled DbcAttrType variant");
        },
        t);
}

static auto attr_value_to_json(const DbcAttrValue& v) -> Json {
    return std::visit(
        [](auto&& a) -> Json {
            using T = std::decay_t<decltype(a)>;
            if constexpr (std::is_same_v<T, DbcAttrValueInt>)
                return {{"kind", "int"}, {"value", a.value}};
            else if constexpr (std::is_same_v<T, DbcAttrValueFloat>)
                return {{"kind", "float"}, {"value", rational_to_json(a.value)}};
            else if constexpr (std::is_same_v<T, DbcAttrValueString>)
                return {{"kind", "string"}, {"value", a.value}};
            else if constexpr (std::is_same_v<T, DbcAttrValueEnum>)
                return {{"kind", "enum"}, {"value", a.value}};
            else if constexpr (std::is_same_v<T, DbcAttrValueHex>)
                return {{"kind", "hex"}, {"value", a.value}};
            else
                static_assert(sizeof(T) == 0, "Unhandled DbcAttrValue variant");
        },
        v);
}

static auto attr_target_to_json(const DbcAttrTarget& t) -> Json {
    return std::visit(
        [](auto&& v) -> Json {
            using T = std::decay_t<decltype(v)>;
            if constexpr (std::is_same_v<T, DbcAttrTargetNetwork>)
                return {{"kind", "network"}};
            else if constexpr (std::is_same_v<T, DbcAttrTargetNode>)
                return {{"kind", "node"}, {"node", v.node}};
            else if constexpr (std::is_same_v<T, DbcAttrTargetMessage>) {
                Json out = {{"kind", "message"}};
                attach_can_id(out, v.id, v.extended);
                return out;
            } else if constexpr (std::is_same_v<T, DbcAttrTargetSignal>) {
                Json out = {{"kind", "signal"}};
                attach_can_id(out, v.id, v.extended);
                out["signal"] = v.signal;
                return out;
            } else if constexpr (std::is_same_v<T, DbcAttrTargetEnvVar>)
                return {{"kind", "envVar"}, {"envVar", v.env_var}};
            else if constexpr (std::is_same_v<T, DbcAttrTargetNodeMsg>) {
                Json out = {{"kind", "nodeMsg"}, {"node", v.node}};
                attach_can_id(out, v.id, v.extended);
                return out;
            } else if constexpr (std::is_same_v<T, DbcAttrTargetNodeSig>) {
                Json out = {{"kind", "nodeSig"}, {"node", v.node}};
                attach_can_id(out, v.id, v.extended);
                out["signal"] = v.signal;
                return out;
            } else
                static_assert(sizeof(T) == 0, "Unhandled DbcAttrTarget variant");
        },
        t);
}

static auto attribute_to_json(const DbcAttribute& a) -> Json {
    return std::visit(
        [](auto&& v) -> Json {
            using T = std::decay_t<decltype(v)>;
            if constexpr (std::is_same_v<T, DbcAttrDef>)
                return {{"kind", "definition"},
                        {"name", v.name},
                        {"scope", attr_scope_to_json(v.scope)},
                        {"attrType", attr_type_to_json(v.attr_type)}};
            else if constexpr (std::is_same_v<T, DbcAttrDefault>)
                return {
                    {"kind", "default"}, {"name", v.name}, {"value", attr_value_to_json(v.value)}};
            else if constexpr (std::is_same_v<T, DbcAttrAssign>)
                return {{"kind", "assignment"},
                        {"name", v.name},
                        {"target", attr_target_to_json(v.target)},
                        {"value", attr_value_to_json(v.value)}};
            else
                static_assert(sizeof(T) == 0, "Unhandled DbcAttribute variant");
        },
        a);
}

// Track E.8 (Plan B): JSON wire form for one unresolved RawValueDesc.
// Mirrors message_to_json's leading {id, extended} pair via attach_can_id.
static auto raw_value_desc_to_json(const DbcRawValueDesc& rvd) -> Json {
    Json entries = Json::array();
    for (const auto& e : rvd.entries)
        entries.push_back({{"value", e.value}, {"description", e.description}});
    Json out = {{"id", can_id_numeric(rvd.can_id)},
                {"signalName", rvd.signal_name},
                {"entries", std::move(entries)}};
    if (can_id_extended(rvd.can_id))
        out["extended"] = true;
    return out;
}

static auto dbc_to_json(const DbcDefinition& dbc) -> Json {
    Json msgs = Json::array();
    for (const auto& m : dbc.messages)
        msgs.push_back(message_to_json(m));
    Json groups = Json::array();
    for (const auto& g : dbc.signal_groups)
        groups.push_back(signal_group_to_json(g));
    Json env_vars = Json::array();
    for (const auto& ev : dbc.environment_vars)
        env_vars.push_back(env_var_to_json(ev));
    Json value_tables = Json::array();
    for (const auto& vt : dbc.value_tables)
        value_tables.push_back(value_table_to_json(vt));
    Json nodes = Json::array();
    for (const auto& n : dbc.nodes)
        nodes.push_back(node_to_json(n));
    Json comments = Json::array();
    for (const auto& c : dbc.comments)
        comments.push_back(comment_to_json(c));
    Json attributes = Json::array();
    for (const auto& a : dbc.attributes)
        attributes.push_back(attribute_to_json(a));
    Json unresolved = Json::array();
    for (const auto& rvd : dbc.unresolved_value_descriptions)
        unresolved.push_back(raw_value_desc_to_json(rvd));
    return {
        {"version", dbc.version},
        {"messages", std::move(msgs)},
        {"signalGroups", std::move(groups)},
        {"environmentVars", std::move(env_vars)},
        {"valueTables", std::move(value_tables)},
        {"nodes", std::move(nodes)},
        {"comments", std::move(comments)},
        {"attributes", std::move(attributes)},
        {"unresolvedValueDescs", std::move(unresolved)},
    };
}

// Map each predicate variant to its JSON representation for the Agda core.
static auto predicate_to_json(const Predicate& p) -> Json {
    return std::visit(
        [](auto&& v) -> Json {
            using T = std::decay_t<decltype(v)>;
            if constexpr (std::is_same_v<T, Equals>)
                return {{"predicate", "equals"},
                        {"signal", v.signal.get()},
                        {"value", rational_to_json(v.value.get())}};
            else if constexpr (std::is_same_v<T, LessThan>)
                return {{"predicate", "lessThan"},
                        {"signal", v.signal.get()},
                        {"value", rational_to_json(v.value.get())}};
            else if constexpr (std::is_same_v<T, GreaterThan>)
                return {{"predicate", "greaterThan"},
                        {"signal", v.signal.get()},
                        {"value", rational_to_json(v.value.get())}};
            else if constexpr (std::is_same_v<T, LessThanOrEqual>)
                return {{"predicate", "lessThanOrEqual"},
                        {"signal", v.signal.get()},
                        {"value", rational_to_json(v.value.get())}};
            else if constexpr (std::is_same_v<T, GreaterThanOrEqual>)
                return {{"predicate", "greaterThanOrEqual"},
                        {"signal", v.signal.get()},
                        {"value", rational_to_json(v.value.get())}};
            else if constexpr (std::is_same_v<T, Between>)
                return {{"predicate", "between"},
                        {"signal", v.signal.get()},
                        {"min", rational_to_json(v.min.get())},
                        {"max", rational_to_json(v.max.get())}};
            else if constexpr (std::is_same_v<T, ChangedBy>)
                return {{"predicate", "changedBy"},
                        {"signal", v.signal.get()},
                        {"delta", v.delta.get()}};
            else if constexpr (std::is_same_v<T, StableWithin>)
                return {{"predicate", "stableWithin"},
                        {"signal", v.signal.get()},
                        {"tolerance", v.tolerance.get()}};
            else
                static_assert(sizeof(T) == 0, "Unhandled predicate type in predicate_to_json");
        },
        p);
}

// Recursively serialize an LTL formula tree to JSON for the Agda core.
static constexpr int max_formula_depth = 100;

static auto formula_to_json(const LtlFormula& f, int depth = 0) -> Json {
    if (depth > max_formula_depth)
        throw std::runtime_error("Formula nesting depth exceeds " +
                                 std::to_string(max_formula_depth));
    return std::visit(
        [depth](auto&& v) -> Json {
            using T = std::decay_t<decltype(v)>;
            if constexpr (std::is_same_v<T, Atomic>)
                return {{"operator", "atomic"}, {"predicate", predicate_to_json(v.predicate)}};
            else if constexpr (std::is_same_v<T, Not>)
                return {{"operator", "not"}, {"formula", formula_to_json(*v.formula, depth + 1)}};
            else if constexpr (std::is_same_v<T, And>)
                return {{"operator", "and"},
                        {"left", formula_to_json(*v.left, depth + 1)},
                        {"right", formula_to_json(*v.right, depth + 1)}};
            else if constexpr (std::is_same_v<T, Or>)
                return {{"operator", "or"},
                        {"left", formula_to_json(*v.left, depth + 1)},
                        {"right", formula_to_json(*v.right, depth + 1)}};
            else if constexpr (std::is_same_v<T, Next>)
                return {{"operator", "next"}, {"formula", formula_to_json(*v.formula, depth + 1)}};
            else if constexpr (std::is_same_v<T, WeakNext>)
                return {{"operator", "weakNext"},
                        {"formula", formula_to_json(*v.formula, depth + 1)}};
            else if constexpr (std::is_same_v<T, Always>)
                return {{"operator", "always"},
                        {"formula", formula_to_json(*v.formula, depth + 1)}};
            else if constexpr (std::is_same_v<T, Eventually>)
                return {{"operator", "eventually"},
                        {"formula", formula_to_json(*v.formula, depth + 1)}};
            else if constexpr (std::is_same_v<T, Until>)
                return {{"operator", "until"},
                        {"left", formula_to_json(*v.left, depth + 1)},
                        {"right", formula_to_json(*v.right, depth + 1)}};
            else if constexpr (std::is_same_v<T, Release>)
                return {{"operator", "release"},
                        {"left", formula_to_json(*v.left, depth + 1)},
                        {"right", formula_to_json(*v.right, depth + 1)}};
            else if constexpr (std::is_same_v<T, MetricAlways>)
                return {{"operator", "metricAlways"},
                        {"timebound", v.bound.count()},
                        {"formula", formula_to_json(*v.formula, depth + 1)}};
            else if constexpr (std::is_same_v<T, MetricEventually>)
                return {{"operator", "metricEventually"},
                        {"timebound", v.bound.count()},
                        {"formula", formula_to_json(*v.formula, depth + 1)}};
            else if constexpr (std::is_same_v<T, MetricUntil>)
                return {{"operator", "metricUntil"},
                        {"timebound", v.bound.count()},
                        {"left", formula_to_json(*v.left, depth + 1)},
                        {"right", formula_to_json(*v.right, depth + 1)}};
            else if constexpr (std::is_same_v<T, MetricRelease>)
                return {{"operator", "metricRelease"},
                        {"timebound", v.bound.count()},
                        {"left", formula_to_json(*v.left, depth + 1)},
                        {"right", formula_to_json(*v.right, depth + 1)}};
            else
                static_assert(sizeof(T) == 0, "Unhandled formula type in formula_to_json");
        },
        static_cast<const LtlFormula::variant&>(f));
}

// ---------------------------------------------------------------------------
// Public serialization functions
// ---------------------------------------------------------------------------

auto serialize_parse_dbc(const DbcDefinition& dbc) -> std::string {
    return Json{{"type", "command"}, {"command", "parseDBC"}, {"dbc", dbc_to_json(dbc)}}.dump();
}

auto serialize_parse_dbc_text(std::string_view text) -> std::string {
    return Json{{"type", "command"}, {"command", "parseDBCText"}, {"text", text}}.dump();
}

auto serialize_parsed_dbc_response(const DbcDefinition& dbc) -> std::string {
    return Json{{"status", "success"}, {"dbc", dbc_to_json(dbc)}, {"warnings", Json::array()}}
        .dump();
}

auto serialize_validate_dbc(const DbcDefinition& dbc) -> std::string {
    return Json{{"type", "command"}, {"command", "validateDBC"}, {"dbc", dbc_to_json(dbc)}}.dump();
}

auto serialize_format_dbc() -> std::string {
    return Json{{"type", "command"}, {"command", "formatDBC"}}.dump();
}

auto serialize_format_dbc_text(const DbcDefinition& dbc) -> std::string {
    return Json{{"type", "command"}, {"command", "formatDBCText"}, {"dbc", dbc_to_json(dbc)}}
        .dump();
}

auto serialize_extract_signals(const CanId& id, Dlc dlc, std::span<const std::byte> data)
    -> std::string {
    // Direct string construction like serialize_send_frame.
    std::string data_str;
    data_str.reserve(data.size() * 4);
    for (std::size_t i = 0; i < data.size(); ++i) {
        if (i > 0)
            data_str += ',';
        data_str += std::to_string(static_cast<std::uint8_t>(data[i]));
    }
    return std::format(R"({{"type":"command","command":"extractAllSignals",)"
                       R"("canId":{},"extended":{},"dlc":{},"data":[{}]}})",
                       can_id_numeric(id), can_id_extended(id) ? "true" : "false", dlc.value(),
                       data_str);
}

auto serialize_set_properties(std::span<const LtlFormula> props) -> std::string {
    Json arr = Json::array();
    for (const auto& f : props)
        arr.push_back(formula_to_json(f));
    return Json{{"type", "command"}, {"command", "setProperties"}, {"properties", std::move(arr)}}
        .dump();
}

auto serialize_start_stream() -> std::string {
    return Json{{"type", "command"}, {"command", "startStream"}}.dump();
}

auto serialize_send_frame(Timestamp ts, const CanId& id, Dlc dlc, std::span<const std::byte> data)
    -> std::string {
    // Used by the mock backend for testing; the real hot path uses binary FFI
    // (send_frame_binary) which bypasses JSON serialization entirely.
    std::string data_str;
    data_str.reserve(data.size() * 4); // "255," = 4 chars max per byte
    for (std::size_t i = 0; i < data.size(); ++i) {
        if (i > 0)
            data_str += ',';
        data_str += std::to_string(static_cast<std::uint8_t>(data[i]));
    }
    return std::format(
        R"({{"type":"data","timestamp":{},"id":{},"extended":{},"dlc":{},"data":[{}]}})",
        ts.count(), can_id_numeric(id), can_id_extended(id) ? "true" : "false", dlc.value(),
        data_str);
}

auto serialize_end_stream() -> std::string {
    return Json{{"type", "command"}, {"command", "endStream"}}.dump();
}

auto serialize_send_error(Timestamp ts) -> std::string {
    return std::format(R"({{"type":"error","timestamp":{}}})", ts.count());
}

auto serialize_send_remote(Timestamp ts, const CanId& id) -> std::string {
    return std::format(R"({{"type":"remote","timestamp":{},"id":{},"extended":{}}})", ts.count(),
                       can_id_numeric(id), can_id_extended(id) ? "true" : "false");
}

} // namespace aletheia::detail
