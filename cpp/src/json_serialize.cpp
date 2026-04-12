// JSON serialization: C++ types → JSON command strings for the Agda core.
#include "detail/json.hpp"

#include <nlohmann/json.hpp>

#include <cstddef>
#include <cstdint>
#include <format>
#include <span>
#include <stdexcept>
#include <string>
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

static auto data_to_json(std::span<const std::byte> data) -> Json {
    Json arr = Json::array();
    for (auto b : data)
        arr.push_back(static_cast<std::uint8_t>(b));
    return arr;
}

static auto signal_value_to_json(const SignalValue& sv) -> Json {
    return {{"name", sv.name.get()}, {"value", sv.value.get()}};
}

static auto signals_to_json(std::span<const SignalValue> signals) -> Json {
    Json arr = Json::array();
    for (const auto& sv : signals)
        arr.push_back(signal_value_to_json(sv));
    return arr;
}

static auto rational_to_json(const Rational& r) -> Json {
    if (r.denominator == 1)
        return r.numerator;
    return {{"numerator", r.numerator}, {"denominator", r.denominator}};
}

static auto presence_to_json(const SignalPresence& p, Json& sig) -> void {
    std::visit(
        [&sig](auto&& v) {
            using T = std::decay_t<decltype(v)>;
            if constexpr (std::is_same_v<T, AlwaysPresent>) {
                // AlwaysPresent is the default — no "presence" key needed.
                // The parser determines presence by checking for "multiplexor".
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
    };
    presence_to_json(s.presence, sig);
    return sig;
}

static auto message_to_json(const DbcMessage& m) -> Json {
    Json sigs = Json::array();
    for (const auto& s : m.signals)
        sigs.push_back(signal_def_to_json(s));
    return {
        {"id", can_id_numeric(m.id)},        {"name", m.name.get()},
        {"dlc", dlc_to_bytes(m.dlc)},        {"sender", m.sender.get()},
        {"extended", can_id_extended(m.id)}, {"signals", std::move(sigs)},
    };
}

static auto dbc_to_json(const DbcDefinition& dbc) -> Json {
    Json msgs = Json::array();
    for (const auto& m : dbc.messages)
        msgs.push_back(message_to_json(m));
    return {{"version", dbc.version}, {"messages", std::move(msgs)}};
}

// Map each predicate variant to its JSON representation for the Agda core.
static auto predicate_to_json(const Predicate& p) -> Json {
    return std::visit(
        [](auto&& v) -> Json {
            using T = std::decay_t<decltype(v)>;
            if constexpr (std::is_same_v<T, Equals>)
                return {
                    {"predicate", "equals"}, {"signal", v.signal.get()}, {"value", v.value.get()}};
            else if constexpr (std::is_same_v<T, LessThan>)
                return {{"predicate", "lessThan"},
                        {"signal", v.signal.get()},
                        {"value", v.value.get()}};
            else if constexpr (std::is_same_v<T, GreaterThan>)
                return {{"predicate", "greaterThan"},
                        {"signal", v.signal.get()},
                        {"value", v.value.get()}};
            else if constexpr (std::is_same_v<T, LessThanOrEqual>)
                return {{"predicate", "lessThanOrEqual"},
                        {"signal", v.signal.get()},
                        {"value", v.value.get()}};
            else if constexpr (std::is_same_v<T, GreaterThanOrEqual>)
                return {{"predicate", "greaterThanOrEqual"},
                        {"signal", v.signal.get()},
                        {"value", v.value.get()}};
            else if constexpr (std::is_same_v<T, Between>)
                return {{"predicate", "between"},
                        {"signal", v.signal.get()},
                        {"min", v.min.get()},
                        {"max", v.max.get()}};
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

auto serialize_validate_dbc(const DbcDefinition& dbc) -> std::string {
    return Json{{"type", "command"}, {"command", "validateDBC"}, {"dbc", dbc_to_json(dbc)}}.dump();
}

auto serialize_format_dbc() -> std::string {
    return Json{{"type", "command"}, {"command", "formatDBC"}}.dump();
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

auto serialize_build_frame(const CanId& id, Dlc dlc, std::span<const SignalValue> signals)
    -> std::string {
    return Json{{"type", "command"},           {"command", "buildFrame"},
                {"canId", can_id_numeric(id)}, {"extended", can_id_extended(id)},
                {"dlc", dlc.value()},          {"signals", signals_to_json(signals)}}
        .dump();
}

auto serialize_update_frame(const CanId& id, Dlc dlc, std::span<const std::byte> data,
                            std::span<const SignalValue> signals) -> std::string {
    return Json{{"type", "command"},
                {"command", "updateFrame"},
                {"canId", can_id_numeric(id)},
                {"extended", can_id_extended(id)},
                {"dlc", dlc.value()},
                {"data", data_to_json(data)},
                {"signals", signals_to_json(signals)}}
        .dump();
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
