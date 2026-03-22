// JSON serialization: C++ types → JSON command strings for the Agda core.
#include "detail/json.hpp"

#include <nlohmann/json.hpp>

#include <cstdint>

using json = nlohmann::json; // NOLINT(readability-identifier-naming)

namespace aletheia::detail {

// ---------------------------------------------------------------------------
// Helpers
// ---------------------------------------------------------------------------

static auto can_id_numeric(const CanId& id) -> std::uint32_t {
    return std::visit([](auto&& v) -> std::uint32_t { return v.value(); }, id);
}

static auto can_id_extended(const CanId& id) -> bool {
    return std::holds_alternative<ExtendedId>(id);
}

static auto data_to_json(std::span<const std::byte, 8> data) -> json {
    json arr = json::array();
    for (auto b : data)
        arr.push_back(static_cast<std::uint8_t>(b));
    return arr;
}

static auto signal_value_to_json(const SignalValue& sv) -> json {
    return {{"name", sv.name.get()}, {"value", sv.value.get()}};
}

static auto signals_to_json(std::span<const SignalValue> signals) -> json {
    json arr = json::array();
    for (const auto& sv : signals)
        arr.push_back(signal_value_to_json(sv));
    return arr;
}

static auto presence_to_json(const SignalPresence& p, json& sig) -> void {
    std::visit(
        [&sig](auto&& v) {
            using T = std::decay_t<decltype(v)>;
            if constexpr (std::is_same_v<T, AlwaysPresent>) {
                sig["presence"] = "always";
            } else {
                sig["multiplexor"] = v.multiplexor.get();
                sig["multiplex_value"] = v.mux_value.get();
            }
        },
        p);
}

static auto signal_def_to_json(const DbcSignal& s) -> json {
    json sig = {
        {"name", s.name.get()},
        {"startBit", s.start_bit.get()},
        {"length", s.bit_length.get()},
        {"byteOrder", s.byte_order == ByteOrder::LittleEndian ? "little_endian" : "big_endian"},
        {"signed", s.is_signed},
        {"factor", s.factor.get()},
        {"offset", s.offset.get()},
        {"minimum", s.minimum.get()},
        {"maximum", s.maximum.get()},
        {"unit", s.unit.get()},
    };
    presence_to_json(s.presence, sig);
    return sig;
}

static auto message_to_json(const DbcMessage& m) -> json {
    json sigs = json::array();
    for (const auto& s : m.signals)
        sigs.push_back(signal_def_to_json(s));
    return {
        {"id", can_id_numeric(m.id)},
        {"name", m.name.get()},
        {"dlc", m.dlc.value()},
        {"sender", m.sender.get()},
        {"extended", can_id_extended(m.id)},
        {"signals", std::move(sigs)},
    };
}

static auto dbc_to_json(const DbcDefinition& dbc) -> json {
    json msgs = json::array();
    for (const auto& m : dbc.messages)
        msgs.push_back(message_to_json(m));
    return {{"version", dbc.version}, {"messages", std::move(msgs)}};
}

// Map each predicate variant to its JSON representation for the Agda core.
static auto predicate_to_json(const Predicate& p) -> json {
    return std::visit(
        [](auto&& v) -> json {
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
            else // ChangedBy
                return {{"predicate", "changedBy"},
                        {"signal", v.signal.get()},
                        {"delta", v.delta.get()}};
        },
        p);
}

static auto formula_to_json(const LtlFormula& f) -> json;

// Recursively serialize an LTL formula tree to JSON for the Agda core.
static auto formula_to_json(const LtlFormula& f) -> json {
    return std::visit(
        [](auto&& v) -> json {
            using T = std::decay_t<decltype(v)>;
            if constexpr (std::is_same_v<T, Atomic>)
                return {{"operator", "atomic"}, {"predicate", predicate_to_json(v.predicate)}};
            else if constexpr (std::is_same_v<T, Not>)
                return {{"operator", "not"}, {"formula", formula_to_json(*v.formula)}};
            else if constexpr (std::is_same_v<T, And>)
                return {{"operator", "and"},
                        {"left", formula_to_json(*v.left)},
                        {"right", formula_to_json(*v.right)}};
            else if constexpr (std::is_same_v<T, Or>)
                return {{"operator", "or"},
                        {"left", formula_to_json(*v.left)},
                        {"right", formula_to_json(*v.right)}};
            else if constexpr (std::is_same_v<T, Next>)
                return {{"operator", "next"}, {"formula", formula_to_json(*v.formula)}};
            else if constexpr (std::is_same_v<T, Always>)
                return {{"operator", "always"}, {"formula", formula_to_json(*v.formula)}};
            else if constexpr (std::is_same_v<T, Eventually>)
                return {{"operator", "eventually"}, {"formula", formula_to_json(*v.formula)}};
            else if constexpr (std::is_same_v<T, Until>)
                return {{"operator", "until"},
                        {"left", formula_to_json(*v.left)},
                        {"right", formula_to_json(*v.right)}};
            else if constexpr (std::is_same_v<T, Release>)
                return {{"operator", "release"},
                        {"left", formula_to_json(*v.left)},
                        {"right", formula_to_json(*v.right)}};
            else if constexpr (std::is_same_v<T, MetricAlways>)
                return {{"operator", "metricAlways"},
                        {"timebound", v.bound.count()},
                        {"formula", formula_to_json(*v.formula)}};
            else if constexpr (std::is_same_v<T, MetricEventually>)
                return {{"operator", "metricEventually"},
                        {"timebound", v.bound.count()},
                        {"formula", formula_to_json(*v.formula)}};
            else if constexpr (std::is_same_v<T, MetricUntil>)
                return {{"operator", "metricUntil"},
                        {"timebound", v.bound.count()},
                        {"left", formula_to_json(*v.left)},
                        {"right", formula_to_json(*v.right)}};
            else // MetricRelease
                return {{"operator", "metricRelease"},
                        {"timebound", v.bound.count()},
                        {"left", formula_to_json(*v.left)},
                        {"right", formula_to_json(*v.right)}};
        },
        static_cast<const LtlFormula::variant&>(f));
}

// ---------------------------------------------------------------------------
// Public serialization functions
// ---------------------------------------------------------------------------

auto serialize_parse_dbc(const DbcDefinition& dbc) -> std::string {
    return json{{"type", "command"}, {"command", "parseDBC"}, {"dbc", dbc_to_json(dbc)}}.dump();
}

auto serialize_validate_dbc(const DbcDefinition& dbc) -> std::string {
    return json{{"type", "command"}, {"command", "validateDBC"}, {"dbc", dbc_to_json(dbc)}}.dump();
}

auto serialize_format_dbc() -> std::string {
    return json{{"type", "command"}, {"command", "formatDBC"}}.dump();
}

auto serialize_extract_signals(const CanId& id, std::span<const std::byte, 8> data) -> std::string {
    return json{{"type", "command"},
                {"command", "extractAllSignals"},
                {"canId", can_id_numeric(id)},
                {"data", data_to_json(data)}}
        .dump();
}

auto serialize_build_frame(const CanId& id, std::span<const SignalValue> signals) -> std::string {
    return json{{"type", "command"},
                {"command", "buildFrame"},
                {"canId", can_id_numeric(id)},
                {"signals", signals_to_json(signals)}}
        .dump();
}

auto serialize_update_frame(const CanId& id, std::span<const std::byte, 8> data,
                            std::span<const SignalValue> signals) -> std::string {
    return json{{"type", "command"},
                {"command", "updateFrame"},
                {"canId", can_id_numeric(id)},
                {"data", data_to_json(data)},
                {"signals", signals_to_json(signals)}}
        .dump();
}

auto serialize_set_properties(std::span<const LtlFormula> props) -> std::string {
    json arr = json::array();
    for (const auto& f : props)
        arr.push_back(formula_to_json(f));
    return json{{"type", "command"}, {"command", "setProperties"}, {"properties", std::move(arr)}}
        .dump();
}

auto serialize_start_stream() -> std::string {
    return json{{"type", "command"}, {"command", "startStream"}}.dump();
}

auto serialize_send_frame(Timestamp ts, const CanId& id, std::span<const std::byte, 8> data)
    -> std::string {
    return json{{"type", "data"},
                {"timestamp", ts.count()},
                {"id", can_id_numeric(id)},
                {"data", data_to_json(data)}}
        .dump();
}

auto serialize_end_stream() -> std::string {
    return json{{"type", "command"}, {"command", "endStream"}}.dump();
}

} // namespace aletheia::detail
