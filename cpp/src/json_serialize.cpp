// SPDX-FileCopyrightText: 2025 Nicolas Pelletier
// SPDX-License-Identifier: BSD-2-Clause
// JSON serialization: C++ types → JSON command strings for the Agda core.
#include "detail/bad_alloc.hpp"
#include "detail/json.hpp"

#include <aletheia/limits.hpp>

#include <nlohmann/json.hpp>

#include <cstdint>
#include <cstdlib>
#include <exception>
#include <expected>
#include <limits>
#include <numeric>
#include <span>
#include <stdexcept>
#include <string>
#include <string_view>
#include <type_traits>
#include <utility>
#include <variant>
#include <vector>

using Json = nlohmann::json;

namespace aletheia::detail {

// `can_id_value` / `can_id_is_extended` live in `<aletheia/types.hpp>`.

static auto rational_to_json(Rational const& r) -> Json {
    // Normalize via gcd so the wire shape is byte-identical with Python's
    // ``Fraction`` (auto-canonical) and Go's parseRational sign convention,
    // preserving cross-binding wire symmetry.
    //
    // Guard ``INT64_MIN`` before ``std::abs``, whose result would overflow:
    // the numerator is emitted raw, un-normalised, rather than faulting. The
    // denominator cannot be it, being positive by construction.
    if (r.numerator() == std::numeric_limits<std::int64_t>::min()) {
        return {{"numerator", r.numerator()}, {"denominator", r.denominator()}};
    }
    auto num = r.numerator();
    auto den = r.denominator();
    // No sign normalisation: a Rational's constructor enforces a positive
    // denominator, so only the numerator can be negative, and the gcd with a
    // positive denominator is at least one.
    auto const g = std::gcd(std::abs(num), den);
    num /= g;
    den /= g;
    if (den == 1)
        return num;
    return {{"numerator", num}, {"denominator", den}};
}

// A JSON array of the elements of `items`, each through `to_json`.
template<typename Range, typename ToJson>
static auto json_array(Range const& items, ToJson to_json) -> Json {
    auto arr = Json::array();
    for (auto const& item : items)
        arr.push_back(to_json(item));
    return arr;
}

static auto presence_to_json(SignalPresence const& p, Json& sig) -> void {
    // Mirror the Agda wire form: every variant carries an explicit
    // "presence" discriminator ("always" / "multiplexed"), as the Agda
    // formatter and the Python and Go serializers do.
    std::visit(
        [&sig](auto&& v) {
            using T = std::decay_t<decltype(v)>;
            if constexpr (std::is_same_v<T, AlwaysPresent>) {
                sig["presence"] = "always";
            } else if constexpr (std::is_same_v<T, Multiplexed>) {
                sig["presence"] = "multiplexed";
                sig["multiplexor"] = v.multiplexor.get();
                sig["multiplex_values"] = json_array(
                    v.multiplex_values, [](MultiplexValue const& mv) { return mv.get(); });
            } else {
                static_assert(sizeof(T) == 0, "Unhandled SignalPresence type");
            }
        },
        p);
}

// The wire form of one {value, description} pair, shared by a signal's inline
// entries and a value table's rows.
static auto value_entry_to_json(DbcValueEntry const& e) -> Json {
    return {{"value", e.value}, {"description", e.description}};
}

// A node-valued field crosses the wire as the plain string it always was; the
// type it carries in the definition says which strings are meant.
static auto node_names_to_json(std::vector<NodeName> const& names) -> Json {
    auto out = Json::array();
    for (auto const& n : names)
        out.emplace_back(n.get());
    return out;
}

static auto signal_def_to_json(DbcSignal const& s) -> Json {
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
        {"receivers", node_names_to_json(s.receivers)},
        {"valueDescriptions", json_array(s.value_descriptions, value_entry_to_json)},
    };
    presence_to_json(s.presence, sig);
    return sig;
}

static auto message_to_json(DbcMessage const& m) -> Json {
    Json msg = {
        {"id", can_id_value(m.id)},
        {"name", m.name.get()},
        {"dlc", dlc_to_bytes(m.dlc)},
        {"sender", m.sender.get()},
        {"senders", node_names_to_json(m.senders)},
        {"signals", json_array(m.signals, signal_def_to_json)},
    };
    // Mirror the Agda wire form: emit "extended" only when the CAN ID is
    // extended (29-bit). Agda omits the field for standard 11-bit frames;
    // its parser accepts both forms but the omit-when-false shape is
    // canonical (matches attach_can_id used for comment / attribute targets,
    // and the same convention enforced by the Python and Go bindings).
    if (can_id_is_extended(m.id))
        msg["extended"] = true;
    return msg;
}

static auto signal_group_to_json(DbcSignalGroup const& g) -> Json {
    return {{"name", g.name},
            {"signals", json_array(g.signals, [](SignalName const& sn) { return sn.get(); })}};
}

static auto env_var_to_json(DbcEnvironmentVar const& ev) -> Json {
    return {
        {"name", ev.name},
        {"varType", static_cast<int>(ev.var_type)},
        {"initial", rational_to_json(ev.initial)},
        {"minimum", rational_to_json(ev.minimum)},
        {"maximum", rational_to_json(ev.maximum)},
    };
}

static auto value_table_to_json(DbcValueTable const& t) -> Json {
    return {{"name", t.name}, {"entries", json_array(t.entries, value_entry_to_json)}};
}

// ---------------------------------------------------------------------------
// Tier 2 serializers (nodes / comments / attributes). Wire format mirrors
// Agda's formatter in src/Aletheia/DBC/Formatter.agda — every tagged union
// carries "kind" as the first field, and extended-ID flags are emitted only
// when true to match formatCANId's omission on 11-bit IDs.
// ---------------------------------------------------------------------------

static auto node_to_json(DbcNode const& n) -> Json {
    return {{"name", n.name.get()}};
}

static auto attach_can_id(Json& obj, CanId const& id) -> void {
    obj["id"] = can_id_value(id);
    if (can_id_is_extended(id))
        obj["extended"] = true;
}

// Comment targets and attribute targets are two variants over the same seven
// shapes, and each shape has one wire form, so one serializer dispatches on
// the members an alternative carries rather than on its type.  A new shape
// fails the final static_assert.
static auto target_to_json(auto const& v) -> Json {
    using T = std::decay_t<decltype(v)>;
    if constexpr (requires {
                      v.node;
                      v.id;
                      v.signal;
                  }) {
        Json out = {{"kind", "nodeSig"}, {"node", v.node.get()}};
        attach_can_id(out, v.id);
        out["signal"] = v.signal;
        return out;
    } else if constexpr (requires {
                             v.node;
                             v.id;
                         }) {
        Json out = {{"kind", "nodeMsg"}, {"node", v.node.get()}};
        attach_can_id(out, v.id);
        return out;
    } else if constexpr (requires {
                             v.id;
                             v.signal;
                         }) {
        Json out = {{"kind", "signal"}};
        attach_can_id(out, v.id);
        out["signal"] = v.signal;
        return out;
    } else if constexpr (requires { v.id; }) {
        Json out = {{"kind", "message"}};
        attach_can_id(out, v.id);
        return out;
    } else if constexpr (requires { v.node; }) {
        return {{"kind", "node"}, {"node", v.node.get()}};
    } else if constexpr (requires { v.env_var; }) {
        return {{"kind", "envVar"}, {"envVar", v.env_var}};
    } else {
        static_assert(std::is_empty_v<T>, "Unhandled target shape in target_to_json");
        return {{"kind", "network"}};
    }
}

static auto comment_target_to_json(DbcCommentTarget const& t) -> Json {
    return std::visit([](auto const& v) { return target_to_json(v); }, t);
}

static auto comment_to_json(DbcComment const& c) -> Json {
    return {{"target", comment_target_to_json(c.target)}, {"text", c.text}};
}

static auto attr_scope_to_json(DbcAttrScope s) -> std::string_view {
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

static auto attr_type_to_json(DbcAttrType const& t) -> Json {
    return std::visit(
        [](auto&& v) -> Json {
            using T = std::decay_t<decltype(v)>;
            if constexpr (std::is_same_v<T, DbcAttrTypeInt>) {
                return {{"kind", "int"}, {"min", v.min}, {"max", v.max}};
            } else if constexpr (std::is_same_v<T, DbcAttrTypeFloat>) {
                return {{"kind", "float"},
                        {"min", rational_to_json(v.min)},
                        {"max", rational_to_json(v.max)}};
            } else if constexpr (std::is_same_v<T, DbcAttrTypeString>) {
                return {{"kind", "string"}};
            } else if constexpr (std::is_same_v<T, DbcAttrTypeEnum>) {
                return {{"kind", "enum"},
                        {"values", json_array(v.values, [](std::string const& e) { return e; })}};
            } else if constexpr (std::is_same_v<T, DbcAttrTypeHex>) {
                return {{"kind", "hex"}, {"min", v.min}, {"max", v.max}};
            } else {
                static_assert(sizeof(T) == 0, "Unhandled DbcAttrType variant");
            }
        },
        t);
}

static auto attr_value_to_json(DbcAttrValue const& v) -> Json {
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

static auto attr_target_to_json(DbcAttrTarget const& t) -> Json {
    return std::visit([](auto const& v) { return target_to_json(v); }, t);
}

static auto attribute_to_json(DbcAttribute const& a) -> Json {
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

// JSON wire form for one unresolved RawValueDesc.
// Mirrors message_to_json's leading {id, extended} pair via attach_can_id.
static auto raw_value_desc_to_json(DbcRawValueDesc const& rvd) -> Json {
    Json out = {{"id", can_id_value(rvd.can_id)},
                {"signalName", rvd.signal_name},
                {"entries", json_array(rvd.entries, value_entry_to_json)}};
    if (can_id_is_extended(rvd.can_id))
        out["extended"] = true;
    return out;
}

static auto dbc_to_json(DbcDefinition const& dbc) -> Json {
    return {
        {"version", dbc.version},
        {"messages", json_array(dbc.messages, message_to_json)},
        {"signalGroups", json_array(dbc.signal_groups, signal_group_to_json)},
        {"environmentVars", json_array(dbc.environment_vars, env_var_to_json)},
        {"valueTables", json_array(dbc.value_tables, value_table_to_json)},
        {"nodes", json_array(dbc.nodes, node_to_json)},
        {"comments", json_array(dbc.comments, comment_to_json)},
        {"attributes", json_array(dbc.attributes, attribute_to_json)},
        {"unresolvedValueDescs", json_array(dbc.unresolved_value_descs, raw_value_desc_to_json)},
    };
}

// The wire tag of each predicate alternative.
template<typename T>
static constexpr auto predicate_tag() -> std::string_view {
    if constexpr (std::is_same_v<T, Equals>)
        return "equals";
    else if constexpr (std::is_same_v<T, LessThan>)
        return "lessThan";
    else if constexpr (std::is_same_v<T, GreaterThan>)
        return "greaterThan";
    else if constexpr (std::is_same_v<T, LessThanOrEqual>)
        return "lessThanOrEqual";
    else if constexpr (std::is_same_v<T, GreaterThanOrEqual>)
        return "greaterThanOrEqual";
    else if constexpr (std::is_same_v<T, Between>)
        return "between";
    else if constexpr (std::is_same_v<T, ChangedBy>)
        return "changedBy";
    else if constexpr (std::is_same_v<T, StableWithin>)
        return "stableWithin";
    else
        static_assert(sizeof(T) == 0, "Unhandled predicate type in predicate_tag");
}

// Map each predicate variant to its JSON representation for the Agda core.
// The five value comparisons differ only in their tag, so the bodies below
// are the four member shapes rather than the eight types.
static auto predicate_to_json(Predicate const& p) -> Json {
    return std::visit(
        [](auto const& v) -> Json {
            using T = std::decay_t<decltype(v)>;
            Json out = {{"predicate", predicate_tag<T>()}, {"signal", v.signal.get()}};
            if constexpr (requires { v.value; }) {
                out["value"] = rational_to_json(v.value.get());
            } else if constexpr (requires {
                                     v.min;
                                     v.max;
                                 }) {
                out["min"] = rational_to_json(v.min.get());
                out["max"] = rational_to_json(v.max.get());
            } else if constexpr (requires { v.delta; }) {
                out["delta"] = rational_to_json(v.delta.get());
            } else if constexpr (requires { v.tolerance; }) {
                out["tolerance"] = rational_to_json(v.tolerance.get());
            } else {
                static_assert(sizeof(T) == 0, "Unhandled predicate shape in predicate_to_json");
            }
            return out;
        },
        p);
}

// The wire tag of each formula alternative.
template<typename T>
static constexpr auto formula_tag() -> std::string_view {
    if constexpr (std::is_same_v<T, Atomic>)
        return "atomic";
    else if constexpr (std::is_same_v<T, Not>)
        return "not";
    else if constexpr (std::is_same_v<T, And>)
        return "and";
    else if constexpr (std::is_same_v<T, Or>)
        return "or";
    else if constexpr (std::is_same_v<T, Next>)
        return "next";
    else if constexpr (std::is_same_v<T, WeakNext>)
        return "weakNext";
    else if constexpr (std::is_same_v<T, Always>)
        return "always";
    else if constexpr (std::is_same_v<T, Eventually>)
        return "eventually";
    else if constexpr (std::is_same_v<T, Until>)
        return "until";
    else if constexpr (std::is_same_v<T, Release>)
        return "release";
    else if constexpr (std::is_same_v<T, MetricAlways>)
        return "metricAlways";
    else if constexpr (std::is_same_v<T, MetricEventually>)
        return "metricEventually";
    else if constexpr (std::is_same_v<T, MetricUntil>)
        return "metricUntil";
    else if constexpr (std::is_same_v<T, MetricRelease>)
        return "metricRelease";
    else
        static_assert(sizeof(T) == 0, "Unhandled formula type in formula_tag");
}

// Recursively serialize an LTL formula tree to JSON for the Agda core.  Each
// alternative contributes its tag and one of four member shapes.  The depth
// cap mirrors the kernel's own (`Aletheia.Limits.max-nesting-depth`, exposed
// as `aletheia::max_nesting_depth`), so a deeper formula is refused here
// rather than serialized and then rejected on the wire.
static auto formula_to_json(LtlFormula const& f, int depth = 0) -> Json {
    if (std::cmp_greater(depth, max_nesting_depth))
        throw std::runtime_error("Formula nesting depth exceeds " +
                                 std::to_string(max_nesting_depth));
    return std::visit(
        [depth](auto const& v) -> Json {
            using T = std::decay_t<decltype(v)>;
            Json out = {{"operator", formula_tag<T>()}};
            if constexpr (requires { v.predicate; }) {
                out["predicate"] = predicate_to_json(v.predicate);
            } else {
                if constexpr (requires { v.bound; }) {
                    out["timebound"] = v.bound.count();
                }
                if constexpr (requires { v.formula; }) {
                    out["formula"] = formula_to_json(*v.formula, depth + 1);
                } else if constexpr (requires {
                                         v.left;
                                         v.right;
                                     }) {
                    out["left"] = formula_to_json(*v.left, depth + 1);
                    out["right"] = formula_to_json(*v.right, depth + 1);
                } else {
                    static_assert(sizeof(T) == 0, "Unhandled formula shape in formula_to_json");
                }
            }
            return out;
        },
        f.value);
}

// ---------------------------------------------------------------------------
// Public serialization functions
// ---------------------------------------------------------------------------

// A command is built from the caller's values, so what the encoder refuses (a
// string that is not UTF-8, a formula nested deeper than the kernel reads) is
// the caller's error: kind Validation, with the encoder's own text.
// The refusal an encoder's exception is, called from the handler so
// std::bad_alloc leaves as it came; one function, whatever the command.
static auto encoder_refusal(std::exception const& e) -> std::unexpected<AletheiaError> {
    rethrow_if_bad_alloc(e);
    return validation_refusal(e.what());
}

template<typename Encode>
static auto encoded(Encode encode, int indent = -1) -> Result<std::string> {
    try {
        return encode().dump(indent);
    } catch (std::exception const& e) {
        return encoder_refusal(e);
    }
}

// Every DBC-carrying command has the same envelope.
static auto dbc_command(std::string_view command, DbcDefinition const& dbc) -> Result<std::string> {
    return encoded(
        [&] { return Json{{"type", "command"}, {"command", command}, {"dbc", dbc_to_json(dbc)}}; });
}

auto serialize_parse_dbc(DbcDefinition const& dbc) -> Result<std::string> {
    return dbc_command("parseDBC", dbc);
}

auto serialize_parse_dbc_text(std::string_view text) -> Result<std::string> {
    return encoded(
        [text] { return Json{{"type", "command"}, {"command", "parseDBCText"}, {"text", text}}; });
}

auto serialize_parsed_dbc_response(DbcDefinition const& dbc) -> std::string {
    return Json{{"status", "success"}, {"dbc", dbc_to_json(dbc)}, {"warnings", Json::array()}}
        .dump();
}

auto serialize_validate_dbc(DbcDefinition const& dbc) -> Result<std::string> {
    return dbc_command("validateDBC", dbc);
}

auto serialize_format_dbc_text(DbcDefinition const& dbc) -> Result<std::string> {
    return dbc_command("formatDBCText", dbc);
}

auto serialize_set_properties(std::span<LtlFormula const> props) -> Result<std::string> {
    return encoded([props] {
        return Json{{"type", "command"},
                    {"command", "setProperties"},
                    {"properties",
                     json_array(props, [](LtlFormula const& f) { return formula_to_json(f); })}};
    });
}

} // namespace aletheia::detail

namespace aletheia {

// Public canonical DBC JSON serializer (declared in <aletheia/dbc.hpp>).
// Reuses the internal `dbc_to_json` encoder, the one the FFI command
// serializers wrap, so the output is the Agda core's canonical form, and it
// refuses what they refuse. Returns a pretty-printed string, keeping nlohmann
// out of the public header.
auto to_canonical_json(DbcDefinition const& dbc) -> Result<std::string> {
    return detail::encoded([&dbc] { return detail::dbc_to_json(dbc); }, 2);
}

} // namespace aletheia
