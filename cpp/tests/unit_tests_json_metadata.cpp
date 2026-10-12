// SPDX-FileCopyrightText: 2025 Nicolas Pelletier
// SPDX-License-Identifier: BSD-2-Clause
// Unit tests: the DBC metadata round-trip through the JSON serializer and
// parser: Tier 1 arrays, Tier 2 nodes, comments and attributes, signal
// receivers, message senders and unresolvedValueDescs.
#include "test_helpers.hpp"

#include <catch2/catch_test_macros.hpp>
#include <catch2/generators/catch_generators.hpp>
#include <catch2/matchers/catch_matchers.hpp>
#include <catch2/matchers/catch_matchers_string.hpp>

#include "detail/json.hpp"
#include <aletheia/aletheia.hpp>

#include <cstdint>
#include <nlohmann/json.hpp>

#include <string>
#include <variant>

using namespace aletheia;
using Json = nlohmann::json;
using aletheia::test::make_test_dbc;
using Catch::Matchers::ContainsSubstring;

// ===========================================================================
// Tier 1 DBC metadata round-trip
// ===========================================================================

TEST_CASE("serialize_parse_dbc emits Tier 1 metadata arrays", "[json][serialize][dbc]") {
    auto dbc = make_test_dbc();
    dbc.signal_groups.push_back(DbcSignalGroup{.name = "Group1", .signals = {SignalName{"Speed"}}});
    dbc.environment_vars.push_back(DbcEnvironmentVar{
        .name = "AmbientTemp",
        .var_type = DbcVarType::Float,
        .initial = Rational{22, 1},
        .minimum = Rational{-40, 1},
        .maximum = Rational{85, 1},
    });
    dbc.value_tables.push_back(DbcValueTable{
        .name = "GearStates",
        .entries = {DbcValueEntry{.value = 0, .description = "Park"},
                    DbcValueEntry{.value = 1, .description = "Drive"}},
    });

    auto const str = detail::serialize_parse_dbc(dbc);
    auto j = Json::parse(str);

    REQUIRE(j["dbc"]["signalGroups"].is_array());
    REQUIRE(j["dbc"]["signalGroups"].size() == 1);
    CHECK(j["dbc"]["signalGroups"][0]["name"] == "Group1");
    CHECK(j["dbc"]["signalGroups"][0]["signals"][0] == "Speed");

    REQUIRE(j["dbc"]["environmentVars"].size() == 1);
    CHECK(j["dbc"]["environmentVars"][0]["name"] == "AmbientTemp");
    CHECK(j["dbc"]["environmentVars"][0]["varType"] == 1);
    CHECK(j["dbc"]["environmentVars"][0]["initial"] == 22);
    CHECK(j["dbc"]["environmentVars"][0]["minimum"] == -40);
    CHECK(j["dbc"]["environmentVars"][0]["maximum"] == 85);

    REQUIRE(j["dbc"]["valueTables"].size() == 1);
    CHECK(j["dbc"]["valueTables"][0]["name"] == "GearStates");
    CHECK(j["dbc"]["valueTables"][0]["entries"].size() == 2);
    CHECK(j["dbc"]["valueTables"][0]["entries"][0]["value"] == 0);
    CHECK(j["dbc"]["valueTables"][0]["entries"][0]["description"] == "Park");
}

TEST_CASE("serialize_parse_dbc emits empty arrays when metadata absent", "[json][serialize][dbc]") {
    auto const dbc = make_test_dbc();
    auto const str = detail::serialize_parse_dbc(dbc);
    auto j = Json::parse(str);
    REQUIRE(j["dbc"]["signalGroups"].is_array());
    CHECK(j["dbc"]["signalGroups"].empty());
    REQUIRE(j["dbc"]["environmentVars"].is_array());
    CHECK(j["dbc"]["environmentVars"].empty());
    REQUIRE(j["dbc"]["valueTables"].is_array());
    CHECK(j["dbc"]["valueTables"].empty());
}

TEST_CASE("parse_dbc_response with Tier 1 metadata", "[json][parse][dbc]") {
    auto result = detail::parse_dbc_response(R"({
        "status": "success",
        "dbc": {
            "version": "1.0",
            "messages": [],
            "signalGroups": [
                {"name": "Engine", "signals": ["RPM", "Torque"]},
                {"name": "Chassis", "signals": ["WheelSpeed"]}
            ],
            "environmentVars": [
                {"name": "AmbientTemp",
                 "varType": 1,
                 "initial": {"numerator": 22, "denominator": 1},
                 "minimum": {"numerator": -40, "denominator": 1},
                 "maximum": {"numerator": 85, "denominator": 1}}
            ],
            "valueTables": [
                {"name": "States",
                 "entries": [
                    {"value": 0, "description": "idle"},
                    {"value": 1, "description": "active"}
                 ]}
            ]
        }
    })");
    REQUIRE(result.has_value());

    REQUIRE(result->signal_groups.size() == 2);
    CHECK(result->signal_groups[0].name == "Engine");
    REQUIRE(result->signal_groups[0].signals.size() == 2);
    CHECK(result->signal_groups[0].signals[0] == SignalName{"RPM"});
    CHECK(result->signal_groups[1].name == "Chassis");

    REQUIRE(result->environment_vars.size() == 1);
    CHECK(result->environment_vars[0].name == "AmbientTemp");
    CHECK(result->environment_vars[0].var_type == DbcVarType::Float);
    CHECK(result->environment_vars[0].initial == Rational{22, 1});
    CHECK(result->environment_vars[0].minimum == Rational{-40, 1});
    CHECK(result->environment_vars[0].maximum == Rational{85, 1});

    REQUIRE(result->value_tables.size() == 1);
    CHECK(result->value_tables[0].name == "States");
    REQUIRE(result->value_tables[0].entries.size() == 2);
    CHECK(result->value_tables[0].entries[0].value == 0);
    CHECK(result->value_tables[0].entries[0].description == "idle");
    CHECK(result->value_tables[0].entries[1].value == 1);
    CHECK(result->value_tables[0].entries[1].description == "active");
}

TEST_CASE("parse_dbc_response accepts missing Tier 1 metadata keys", "[json][parse][dbc]") {
    // Wire format compatibility — pre-Tier-1 responses omit the new fields;
    // they should parse as empty vectors, not errors.
    auto result = detail::parse_dbc_response(R"({
        "status": "success",
        "dbc": {"version": "1.0", "messages": []}
    })");
    REQUIRE(result.has_value());
    CHECK(result->signal_groups.empty());
    CHECK(result->environment_vars.empty());
    CHECK(result->value_tables.empty());
}

TEST_CASE("parse_dbc_response rejects unknown varType", "[json][parse][dbc][error]") {
    // Past the known types on either side: a negative type is an integer the
    // reader accepts and the type switch refuses, by the same words.
    auto const var_type = GENERATE(7, -1);
    auto result = detail::parse_dbc_response(R"({
        "status": "success",
        "dbc": {
            "version": "1.0",
            "messages": [],
            "environmentVars": [
                {"name": "Bad", "varType": )" +
                                             std::to_string(var_type) +
                                             R"(,
                 "initial": 0, "minimum": 0, "maximum": 0}
            ]
        }
    })");
    CHECK_FALSE(result.has_value());
    CHECK(result.error().kind() == ErrorKind::Protocol);
    CHECK_THAT(std::string{result.error().message()},
               ContainsSubstring("Unknown environment variable type " + std::to_string(var_type)));
}

TEST_CASE("parse_dbc_response refuses a varType wider than its integer",
          "[json][parse][dbc][error]") {
    // The type is read as a 32-bit integer; a value past that width on either
    // side is refused as out of range before the type switch ever sees a
    // truncation of it.
    auto const wide = GENERATE(std::int64_t{3000000000LL}, std::int64_t{-3000000000LL});
    auto result = detail::parse_dbc_response(R"({
        "status": "success",
        "dbc": {
            "version": "1.0",
            "messages": [],
            "environmentVars": [
                {"name": "Wide", "varType": )" +
                                             std::to_string(wide) +
                                             R"(,
                 "initial": 0, "minimum": 0, "maximum": 0}
            ]
        }
    })");
    CHECK_FALSE(result.has_value());
    CHECK_THAT(std::string{result.error().message()}, ContainsSubstring("varType is out of range"));
}

TEST_CASE("parse_dbc_response env var preserves exact rationals", "[json][parse][dbc]") {
    auto result = detail::parse_dbc_response(R"({
        "status": "success",
        "dbc": {
            "version": "",
            "messages": [],
            "environmentVars": [
                {"name": "Precise", "varType": 1,
                 "initial": {"numerator": 1, "denominator": 10},
                 "minimum": {"numerator": -1, "denominator": 3},
                 "maximum": {"numerator": 22, "denominator": 7}}
            ]
        }
    })");
    REQUIRE(result.has_value());
    REQUIRE(result->environment_vars.size() == 1);
    auto const& ev = result->environment_vars[0];
    CHECK(ev.initial == Rational{1, 10});
    CHECK(ev.minimum == Rational{-1, 3});
    CHECK(ev.maximum == Rational{22, 7});
}

// ===========================================================================
// Tier 2 DBC metadata round-trip — nodes, comments, attributes
// ===========================================================================

// The targets carry a validated identifier now, so the tests name one the same
// way the parser does: by value and by width.
static auto std_can_id(std::uint32_t v) -> CanId {
    return CanId{StandardId::create(static_cast<std::uint16_t>(v)).value()};
}
static auto ext_can_id(std::uint32_t v) -> CanId {
    return CanId{ExtendedId::create(v).value()};
}

// A DBC carrying one of every Tier 2 shape: nodes, each comment target,
// each attribute definition kind, a default and an assignment.
// Every attribute shape the wire carries: a definition per scope and per
// type, one default and one assignment.
static void add_tier2_attributes(DbcDefinition& dbc) {
    dbc.attributes.emplace_back(DbcAttrDef{
        .name = "GenMsgCycleTime",
        .scope = DbcAttrScope::Message,
        .attr_type = DbcAttrTypeInt{.min = 0, .max = 10000},
    });
    dbc.attributes.emplace_back(DbcAttrDef{
        .name = "SignalGain",
        .scope = DbcAttrScope::Signal,
        .attr_type = DbcAttrTypeFloat{.min = Rational{-1, 2}, .max = Rational{22, 7}},
    });
    dbc.attributes.emplace_back(DbcAttrDef{
        .name = "BusName",
        .scope = DbcAttrScope::Network,
        .attr_type = DbcAttrTypeString{},
    });
    dbc.attributes.emplace_back(DbcAttrDef{
        .name = "ModuleType",
        .scope = DbcAttrScope::Node,
        .attr_type = DbcAttrTypeEnum{.values = {"ECU", "Gateway", "Sensor"}},
    });
    dbc.attributes.emplace_back(DbcAttrDef{
        .name = "AddressMask",
        .scope = DbcAttrScope::Message,
        .attr_type = DbcAttrTypeHex{.min = 0, .max = 65535},
    });
    dbc.attributes.emplace_back(DbcAttrDefault{
        .name = "GenMsgCycleTime",
        .value = DbcAttrValueInt{.value = 100},
    });
    dbc.attributes.emplace_back(DbcAttrAssign{
        .name = "GenMsgCycleTime",
        .target = DbcAttrTargetMessage{.id = std_can_id(256)},
        .value = DbcAttrValueInt{.value = 20},
    });
    dbc.attributes.emplace_back(DbcAttrAssign{
        .name = "SignalGain",
        .target = DbcAttrTargetSignal{.id = ext_can_id(512), .signal = "Torque"},
        .value = DbcAttrValueFloat{.value = Rational{3, 4}},
    });
    dbc.attributes.emplace_back(DbcAttrAssign{
        .name = "ModuleType",
        .target = DbcAttrTargetNode{.node = NodeName{"ECU1"}},
        .value = DbcAttrValueEnum{.value = 0},
    });
    dbc.attributes.emplace_back(DbcAttrAssign{
        .name = "SenderRole",
        .target = DbcAttrTargetNodeMsg{.node = NodeName{"ECU1"}, .id = std_can_id(256)},
        .value = DbcAttrValueString{.value = "producer"},
    });
    dbc.attributes.emplace_back(DbcAttrAssign{
        .name = "SignalAccess",
        .target = DbcAttrTargetNodeSig{.node = NodeName{"ECU1"},
                                       .id = ext_can_id(512),
                                       .signal = "Torque"},
        .value = DbcAttrValueHex{.value = 255},
    });
    dbc.attributes.emplace_back(DbcAttrAssign{
        .name = "BusType",
        .target = DbcAttrTargetNetwork{},
        .value = DbcAttrValueString{.value = "CAN"},
    });
    dbc.attributes.emplace_back(DbcAttrAssign{
        .name = "EnvUnit",
        .target = DbcAttrTargetEnvVar{.env_var = "AmbientTemp"},
        .value = DbcAttrValueString{.value = "degC"},
    });
}

static auto make_tier2_dbc() -> DbcDefinition {
    auto dbc = make_test_dbc();
    dbc.nodes.push_back(DbcNode{.name = NodeName{"ECU1"}});
    dbc.nodes.push_back(DbcNode{.name = NodeName{"Gateway"}});

    dbc.comments.push_back(DbcComment{
        .target = DbcCommentTargetNetwork{},
        .text = "Vehicle network",
    });
    dbc.comments.push_back(DbcComment{
        .target = DbcCommentTargetNode{.node = NodeName{"ECU1"}},
        .text = "Engine control unit",
    });
    dbc.comments.push_back(DbcComment{
        .target = DbcCommentTargetMessage{.id = std_can_id(256)},
        .text = "Engine status message",
    });
    dbc.comments.push_back(DbcComment{
        .target = DbcCommentTargetSignal{.id = ext_can_id(512), .signal = "Torque"},
        .text = "Requested torque",
    });
    dbc.comments.push_back(DbcComment{
        .target = DbcCommentTargetEnvVar{.env_var = "AmbientTemp"},
        .text = "Ambient temperature sensor",
    });
    add_tier2_attributes(dbc);
    return dbc;
}

TEST_CASE("Tier 2 DBC metadata serializes to the documented wire shape",
          "[json][serialize][parse][dbc][tier2]") {
    auto const dbc = make_tier2_dbc();
    auto const str = detail::serialize_parse_dbc(dbc);
    auto const j = Json::parse(str);

    // Confirm wire shape: every tagged union carries "kind" first.
    REQUIRE(j["dbc"]["nodes"].is_array());
    REQUIRE(j["dbc"]["nodes"].size() == 2);
    CHECK(j["dbc"]["nodes"][0]["name"] == "ECU1");

    REQUIRE(j["dbc"]["comments"].size() == 5);
    CHECK(j["dbc"]["comments"][0]["target"]["kind"] == "network");
    CHECK(j["dbc"]["comments"][3]["target"]["kind"] == "signal");
    CHECK(j["dbc"]["comments"][3]["target"]["extended"] == true);

    REQUIRE(j["dbc"]["attributes"].size() == 13);
    CHECK(j["dbc"]["attributes"][0]["kind"] == "definition");
    CHECK(j["dbc"]["attributes"][0]["attrType"]["kind"] == "int");
    // Float attribute values serialize as {numerator, denominator} dicts
    // — matches Python's Fraction, drifts under double.
    CHECK(j["dbc"]["attributes"][1]["attrType"]["min"]["numerator"] == -1);
    CHECK(j["dbc"]["attributes"][1]["attrType"]["min"]["denominator"] == 2);
}

TEST_CASE("Tier 2 attribute bounds and values survive the parse leg, each one",
          "[json][serialize][parse][dbc][tier2]") {
    // Every integer the attributes carry, read back, including the zeros: a
    // bound the parse leg replaced with a constant would go unseen where only
    // the other bound is asserted.
    auto const dbc = make_tier2_dbc();
    auto const result = detail::parse_dbc_response(detail::serialize_parsed_dbc_response(dbc));
    REQUIRE(result.has_value());
    REQUIRE(result->attributes.size() == 13);
    auto const& def_int = std::get<DbcAttrDef>(result->attributes[0]);
    CHECK(std::get<DbcAttrTypeInt>(def_int.attr_type).min == 0);
    CHECK(std::get<DbcAttrTypeInt>(def_int.attr_type).max == 10000);
    auto const& def_hex = std::get<DbcAttrDef>(result->attributes[4]);
    CHECK(std::get<DbcAttrTypeHex>(def_hex.attr_type).min == 0);
    CHECK(std::get<DbcAttrTypeHex>(def_hex.attr_type).max == 65535);
    auto const& assign_enum = std::get<DbcAttrAssign>(result->attributes[8]);
    CHECK(std::get<DbcAttrValueEnum>(assign_enum.value).value == 0);
}

TEST_CASE("Tier 2 DBC metadata survives the parse leg of the round-trip",
          "[json][serialize][parse][dbc][tier2]") {
    auto const dbc = make_tier2_dbc();
    auto const str = detail::serialize_parse_dbc(dbc);
    auto const j = Json::parse(str);

    // Route the serialized JSON through parse_dbc_response (wrap as success
    // envelope) to exercise the parser leg of the round-trip.
    const Json envelope = {{"status", "success"}, {"dbc", j["dbc"]}};
    auto result = detail::parse_dbc_response(envelope.dump());
    REQUIRE(result.has_value());

    REQUIRE(result->nodes.size() == 2);
    CHECK(result->nodes[0].name.get() == "ECU1");
    CHECK(result->nodes[1].name.get() == "Gateway");

    REQUIRE(result->comments.size() == 5);
    CHECK(std::holds_alternative<DbcCommentTargetNetwork>(result->comments[0].target));
    CHECK(std::get<DbcCommentTargetNode>(result->comments[1].target).node.get() == "ECU1");
    auto const& msg_ct = std::get<DbcCommentTargetMessage>(result->comments[2].target);
    CHECK(can_id_value(msg_ct.id) == 256);
    CHECK_FALSE(can_id_is_extended(msg_ct.id));
    auto const& sig_ct = std::get<DbcCommentTargetSignal>(result->comments[3].target);
    CHECK(can_id_value(sig_ct.id) == 512);
    CHECK(can_id_is_extended(sig_ct.id));
    CHECK(sig_ct.signal == "Torque");
    CHECK(std::get<DbcCommentTargetEnvVar>(result->comments[4].target).env_var == "AmbientTemp");

    REQUIRE(result->attributes.size() == 13);
    // Definitions
    auto const& def_int = std::get<DbcAttrDef>(result->attributes[0]);
    CHECK(def_int.name == "GenMsgCycleTime");
    CHECK(def_int.scope == DbcAttrScope::Message);
    CHECK(std::get<DbcAttrTypeInt>(def_int.attr_type).max == 10000);
    auto const& def_float = std::get<DbcAttrDef>(result->attributes[1]);
    auto const& float_bounds = std::get<DbcAttrTypeFloat>(def_float.attr_type);
    CHECK(float_bounds.min == Rational{-1, 2});
    CHECK(float_bounds.max == Rational{22, 7});
    auto const& def_enum = std::get<DbcAttrDef>(result->attributes[3]);
    auto const& enum_labels = std::get<DbcAttrTypeEnum>(def_enum.attr_type);
    REQUIRE(enum_labels.values.size() == 3);
    CHECK(enum_labels.values[1] == "Gateway");

    // Default
    auto const& dflt = std::get<DbcAttrDefault>(result->attributes[5]);
    CHECK(dflt.name == "GenMsgCycleTime");
    CHECK(std::get<DbcAttrValueInt>(dflt.value).value == 100);

    // Assignments (target + value parity)
    auto const& assign_sig = std::get<DbcAttrAssign>(result->attributes[7]);
    auto const& sig_tgt = std::get<DbcAttrTargetSignal>(assign_sig.target);
    CHECK(can_id_value(sig_tgt.id) == 512);
    CHECK(can_id_is_extended(sig_tgt.id));
    CHECK(sig_tgt.signal == "Torque");
    CHECK(std::get<DbcAttrValueFloat>(assign_sig.value).value == Rational{3, 4});

    auto const& assign_nm = std::get<DbcAttrAssign>(result->attributes[9]);
    auto const& nm_tgt = std::get<DbcAttrTargetNodeMsg>(assign_nm.target);
    CHECK(nm_tgt.node.get() == "ECU1");
    CHECK(can_id_value(nm_tgt.id) == 256);
    CHECK_FALSE(can_id_is_extended(nm_tgt.id));

    auto const& assign_ns = std::get<DbcAttrAssign>(result->attributes[10]);
    auto const& ns_tgt = std::get<DbcAttrTargetNodeSig>(assign_ns.target);
    CHECK(ns_tgt.node.get() == "ECU1");
    CHECK(ns_tgt.signal == "Torque");
    CHECK(can_id_is_extended(ns_tgt.id));
    CHECK(std::get<DbcAttrValueHex>(assign_ns.value).value == 255);

    auto const& assign_net = std::get<DbcAttrAssign>(result->attributes[11]);
    CHECK(std::holds_alternative<DbcAttrTargetNetwork>(assign_net.target));
    CHECK(std::get<DbcAttrValueString>(assign_net.value).value == "CAN");

    auto const& assign_env = std::get<DbcAttrAssign>(result->attributes[12]);
    CHECK(std::get<DbcAttrTargetEnvVar>(assign_env.target).env_var == "AmbientTemp");
    CHECK(std::get<DbcAttrValueString>(assign_env.value).value == "degC");
}

TEST_CASE("a target naming an identifier too wide for its width is refused",
          "[json][parse][dbc][tier2]") {
    // The target carries the same validated identifier a message does, so a
    // value outside the width it claims is refused at the parse boundary rather
    // than stored and handed on. 0x800 needs twelve bits; the target says the
    // identifier is standard, which is eleven.
    auto const make = [](const char* target) {
        return std::string{R"({"status":"success","dbc":{"version":"1.0","messages":[],)"} +
               R"("comments":[{"target":)" + target + R"(,"text":"x"}]}})";
    };
    auto too_wide = detail::parse_dbc_response(make(R"({"kind":"message","id":2048})"));
    REQUIRE_FALSE(too_wide.has_value());
    CHECK(std::string{too_wide.error().message()}.contains("2048"));

    // The same value is fine when the target says the identifier is extended.
    auto as_extended =
        detail::parse_dbc_response(make(R"({"kind":"message","id":2048,"extended":true})"));
    REQUIRE(as_extended.has_value());
    REQUIRE(as_extended->comments.size() == 1);
    auto const& t = std::get<DbcCommentTargetMessage>(as_extended->comments[0].target);
    CHECK(can_id_value(t.id) == 2048);
    CHECK(can_id_is_extended(t.id));
}

TEST_CASE("DbcSignal.receivers round-trips through serialize + parse",
          "[json][serialize][parse][dbc][tier2]") {
    auto dbc = make_test_dbc();
    REQUIRE(dbc.messages.size() == 1);
    REQUIRE(dbc.messages[0].signals.size() == 1);
    dbc.messages[0].signals[0].receivers = {NodeName{"ECU_A"}, NodeName{"ECU_B"}};

    auto const str = detail::serialize_parse_dbc(dbc);
    auto j = Json::parse(str);

    REQUIRE(j["dbc"]["messages"][0]["signals"][0]["receivers"].is_array());
    CHECK(j["dbc"]["messages"][0]["signals"][0]["receivers"].size() == 2);
    CHECK(j["dbc"]["messages"][0]["signals"][0]["receivers"][0] == "ECU_A");
    CHECK(j["dbc"]["messages"][0]["signals"][0]["receivers"][1] == "ECU_B");

    const Json envelope = {{"status", "success"}, {"dbc", j["dbc"]}};
    auto result = detail::parse_dbc_response(envelope.dump());
    REQUIRE(result.has_value());
    REQUIRE(result->messages.size() == 1);
    REQUIRE(result->messages[0].signals.size() == 1);
    auto const& parsed = result->messages[0].signals[0].receivers;
    REQUIRE(parsed.size() == 2);
    CHECK(parsed[0].get() == "ECU_A");
    CHECK(parsed[1].get() == "ECU_B");
}

TEST_CASE("parse_dbc_response accepts missing receivers field", "[json][parse][dbc][tier2]") {
    // Older snapshots / hand-written JSON may omit the receivers key entirely;
    // the parser defaults to an empty vector rather than rejecting.
    auto result = detail::parse_dbc_response(R"({
        "status": "success",
        "dbc": {"version": "1.0", "messages": [{
            "id": 256, "name": "M", "dlc": 8, "sender": "ECU", "extended": false,
            "signals": [{
                "name": "S", "startBit": 0, "length": 8, "byteOrder": "little_endian",
                "signed": false, "factor": {"numerator": 1, "denominator": 1},
                "offset": {"numerator": 0, "denominator": 1},
                "minimum": {"numerator": 0, "denominator": 1},
                "maximum": {"numerator": 255, "denominator": 1},
                "unit": "", "presence": "always"
            }]
        }]}
    })");
    REQUIRE(result.has_value());
    REQUIRE(result->messages.size() == 1);
    REQUIRE(result->messages[0].signals.size() == 1);
    CHECK(result->messages[0].signals[0].receivers.empty());
}

TEST_CASE("DbcMessage.senders round-trips through serialize + parse",
          "[json][serialize][parse][dbc][tier2]") {
    // BO_TX_BU_ additional transmitters: primary stays in `sender`, extras
    // in `senders`. Mirrors the Python split — Agda treats both the same
    // way for UnknownMessageSender validation but the disambiguated message
    // text differs.
    auto dbc = make_test_dbc();
    REQUIRE(dbc.messages.size() == 1);
    dbc.messages[0].senders = {NodeName{"ECU_B"}, NodeName{"ECU_C"}};

    auto const str = detail::serialize_parse_dbc(dbc);
    auto j = Json::parse(str);

    REQUIRE(j["dbc"]["messages"][0]["senders"].is_array());
    CHECK(j["dbc"]["messages"][0]["senders"].size() == 2);
    CHECK(j["dbc"]["messages"][0]["senders"][0] == "ECU_B");
    CHECK(j["dbc"]["messages"][0]["senders"][1] == "ECU_C");

    const Json envelope = {{"status", "success"}, {"dbc", j["dbc"]}};
    auto result = detail::parse_dbc_response(envelope.dump());
    REQUIRE(result.has_value());
    REQUIRE(result->messages.size() == 1);
    auto const& parsed = result->messages[0].senders;
    REQUIRE(parsed.size() == 2);
    CHECK(parsed[0].get() == "ECU_B");
    CHECK(parsed[1].get() == "ECU_C");
}

TEST_CASE("parse_dbc_response accepts missing senders field", "[json][parse][dbc][tier2]") {
    // Older snapshots / hand-written JSON may omit `senders`; default to
    // an empty vector rather than rejecting.
    auto result = detail::parse_dbc_response(R"({
        "status": "success",
        "dbc": {"version": "1.0", "messages": [{
            "id": 256, "name": "M", "dlc": 8, "sender": "ECU", "extended": false,
            "signals": []
        }]}
    })");
    REQUIRE(result.has_value());
    REQUIRE(result->messages.size() == 1);
    CHECK(result->messages[0].senders.empty());
}

TEST_CASE("parse_dbc_response accepts missing Tier 2 metadata keys", "[json][parse][dbc][tier2]") {
    auto result = detail::parse_dbc_response(R"({
        "status": "success",
        "dbc": {"version": "1.0", "messages": []}
    })");
    REQUIRE(result.has_value());
    CHECK(result->nodes.empty());
    CHECK(result->comments.empty());
    CHECK(result->attributes.empty());
}

TEST_CASE("parse_dbc_response rejects unknown comment target kind",
          "[json][parse][dbc][tier2][error]") {
    auto result = detail::parse_dbc_response(R"({
        "status": "success",
        "dbc": {"version": "1.0", "messages": [],
                "comments": [{"target": {"kind": "galaxy"}, "text": "x"}]}
    })");
    CHECK_FALSE(result.has_value());
    CHECK(result.error().kind() == ErrorKind::Protocol);
    CHECK_THAT(std::string{result.error().message()}, ContainsSubstring("comment target kind"));
}

// ===========================================================================
// `unresolvedValueDescs` parse / roundtrip
//
// The field travels in both directions: the serializer emits it and the parser
// decodes it. These cases pin the parse arm, which is the half a refactor can
// drop without the serializer noticing.
// ===========================================================================

TEST_CASE("parse_dbc_response decodes unresolvedValueDescs", "[json][parse][dbc]") {
    auto result = detail::parse_dbc_response(R"({
        "status": "success",
        "dbc": {
            "version": "1.0",
            "messages": [],
            "unresolvedValueDescs": [
                {"id": 256,
                 "signalName": "PhantomSignal",
                 "entries": [
                    {"value": 0, "description": "Off"},
                    {"value": 1, "description": "On"}
                 ]},
                {"id": 1234567,
                 "extended": true,
                 "signalName": "GhostSignal",
                 "entries": [{"value": 7, "description": "Lucky"}]}
            ]
        }
    })");
    REQUIRE(result.has_value());
    REQUIRE(result->unresolved_value_descs.size() == 2);

    auto const& rvd0 = result->unresolved_value_descs[0];
    CHECK(std::holds_alternative<StandardId>(rvd0.can_id));
    CHECK(std::get<StandardId>(rvd0.can_id).value() == 256);
    CHECK(rvd0.signal_name == "PhantomSignal");
    REQUIRE(rvd0.entries.size() == 2);
    CHECK(rvd0.entries[0].value == 0);
    CHECK(rvd0.entries[0].description == "Off");
    CHECK(rvd0.entries[1].value == 1);
    CHECK(rvd0.entries[1].description == "On");

    auto const& rvd1 = result->unresolved_value_descs[1];
    CHECK(std::holds_alternative<ExtendedId>(rvd1.can_id));
    CHECK(std::get<ExtendedId>(rvd1.can_id).value() == 1234567);
    CHECK(rvd1.signal_name == "GhostSignal");
    REQUIRE(rvd1.entries.size() == 1);
    CHECK(rvd1.entries[0].value == 7);
    CHECK(rvd1.entries[0].description == "Lucky");
}

TEST_CASE("DbcDefinition unresolvedValueDescs survives serialize -> parse",
          "[json][serialize][parse][dbc][regression]") {
    // Wire-roundtrip parity with Python (`_helpers.py::_normalize_raw_value_desc`)
    // and Go (`json_dbc.go::parseUnresolvedValueDescs`). Originally the C++ parser
    // dropped `unresolvedValueDescs` silently; this test pins the field through
    // the full serialize-then-parse cycle.
    auto dbc = make_test_dbc();
    dbc.unresolved_value_descs.push_back(DbcRawValueDesc{
        .can_id = CanId{*StandardId::create(0x100)},
        .signal_name = "Phantom",
        .entries = {DbcValueEntry{.value = 0, .description = "Off"},
                    DbcValueEntry{.value = 1, .description = "On"}},
    });

    // Serialize via the parse_dbc COMMAND form — the "dbc" body shape is
    // identical to the "dbc" body shape in a parse_dbc RESPONSE, so the
    // wire shape under test is the same one the FFI emits and consumes.
    auto const cmd_str = detail::serialize_parse_dbc(dbc);
    auto cmd_j = Json::parse(cmd_str);
    REQUIRE(cmd_j.contains("dbc"));
    REQUIRE(cmd_j["dbc"]["unresolvedValueDescs"].is_array());
    REQUIRE(cmd_j["dbc"]["unresolvedValueDescs"].size() == 1);

    // Re-wrap the dbc body as a success response and parse it back.
    const Json response = {{"status", "success"}, {"dbc", cmd_j["dbc"]}};
    auto parsed = detail::parse_dbc_response(response.dump());
    REQUIRE(parsed.has_value());
    REQUIRE(parsed->unresolved_value_descs.size() == 1);
    auto const& rvd = parsed->unresolved_value_descs[0];
    CHECK(std::holds_alternative<StandardId>(rvd.can_id));
    CHECK(std::get<StandardId>(rvd.can_id).value() == 0x100);
    CHECK(rvd.signal_name == "Phantom");
    REQUIRE(rvd.entries.size() == 2);
    CHECK(rvd.entries[0].value == 0);
    CHECK(rvd.entries[0].description == "Off");
    CHECK(rvd.entries[1].value == 1);
    CHECK(rvd.entries[1].description == "On");
}

TEST_CASE("parse_dbc_response accepts missing unresolvedValueDescs", "[json][parse][dbc]") {
    auto result = detail::parse_dbc_response(R"({
        "status": "success",
        "dbc": {"version": "1.0", "messages": []}
    })");
    REQUIRE(result.has_value());
    CHECK(result->unresolved_value_descs.empty());
}
