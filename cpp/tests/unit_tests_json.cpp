// SPDX-License-Identifier: BSD-2-Clause
// Unit tests: JSON serialize/parse + formula pretty-printer.
//
// Covers detail::serialize_* and detail::parse_* for commands, responses,
// DBC trees, frame payloads, and LTL formulas. Also exercises the public
// format_formula() helper used by violation enrichment to render a failed
// formula into a human-readable string.
#include "test_helpers.hpp"

#include <catch2/catch_approx.hpp>
#include <catch2/catch_test_macros.hpp>
#include <catch2/matchers/catch_matchers.hpp>
#include <catch2/matchers/catch_matchers_string.hpp>

#include "detail/json.hpp"
#include <aletheia/aletheia.hpp>
#include <aletheia/enrich.hpp>

#include <nlohmann/json.hpp>

#include <cstddef>
#include <memory>
#include <string>
#include <utility>
#include <variant>
#include <vector>

using namespace aletheia;
using json = nlohmann::json;
using aletheia::test::make_test_dbc;
using Catch::Matchers::ContainsSubstring;

// ===========================================================================
// JSON Serialization tests
// ===========================================================================

TEST_CASE("serialize_parse_dbc produces valid JSON", "[json][serialize]") {
    auto dbc = make_test_dbc();
    auto str = detail::serialize_parse_dbc(dbc);
    auto j = json::parse(str);

    CHECK(j["type"] == "command");
    CHECK(j["command"] == "parseDBC");
    CHECK(j["dbc"]["version"] == "1.0");
    CHECK(j["dbc"]["messages"].size() == 1);

    auto& msg = j["dbc"]["messages"][0];
    CHECK(msg["id"] == 0x100);
    CHECK(msg["name"] == "VehicleSpeed");
    CHECK(msg["dlc"] == 8);
    CHECK(msg["sender"] == "ECU1");
    CHECK(msg["extended"] == false);

    auto& sig = msg["signals"][0];
    CHECK(sig["name"] == "Speed");
    CHECK(sig["startBit"] == 0);
    CHECK(sig["length"] == 16);
    CHECK(sig["byteOrder"] == "little_endian");
    CHECK(sig["signed"] == false);
    CHECK(sig["factor"]["numerator"] == 1);
    CHECK(sig["factor"]["denominator"] == 10);
    CHECK(sig["offset"] == 0);
    CHECK(sig["minimum"] == 0);
    CHECK(sig["maximum"] == 300);
    CHECK(sig["unit"] == "km/h");
    CHECK_FALSE(sig.contains("presence"));
}

TEST_CASE("serialize_extract_signals produces correct JSON", "[json][serialize]") {
    auto id = CanId{StandardId::create(0x100).value()};
    auto dlc = Dlc::create(8).value();
    FramePayload data{std::byte{0xE8}, std::byte{0x03}, std::byte{0}, std::byte{0},
                      std::byte{0},    std::byte{0},    std::byte{0}, std::byte{0}};
    auto str = detail::serialize_extract_signals(id, dlc, data);
    auto j = json::parse(str);

    CHECK(j["command"] == "extractAllSignals");
    CHECK(j["canId"] == 0x100);
    CHECK(j["dlc"] == 8);
    CHECK(j["data"].size() == 8);
    CHECK(j["data"][0] == 0xE8);
    CHECK(j["data"][1] == 0x03);
}

TEST_CASE("serialize_set_properties produces correct JSON", "[json][serialize]") {
    auto formula = ltl::always(
        ltl::atomic(ltl::less_than(SignalName{"Speed"}, PhysicalValue{Rational{220, 1}})));
    std::vector<LtlFormula> props;
    props.push_back(std::move(formula));
    auto str = detail::serialize_set_properties(props);
    auto j = json::parse(str);

    CHECK(j["command"] == "setProperties");
    CHECK(j["properties"].size() == 1);
    CHECK(j["properties"][0]["operator"] == "always");
    CHECK(j["properties"][0]["formula"]["operator"] == "atomic");
    CHECK(j["properties"][0]["formula"]["predicate"]["predicate"] == "lessThan");
    CHECK(j["properties"][0]["formula"]["predicate"]["signal"] == "Speed");
    CHECK(j["properties"][0]["formula"]["predicate"]["value"] == Catch::Approx(220.0));
}

TEST_CASE("serialize_send_frame produces correct JSON", "[json][serialize]") {
    auto id = CanId{StandardId::create(0x100).value()};
    auto dlc = Dlc::create(8).value();
    FramePayload data(8, std::byte{0});
    auto str = detail::serialize_send_frame(Timestamp{1'000'000}, id, dlc, data);
    auto j = json::parse(str);

    CHECK(j["type"] == "data");
    CHECK(j["timestamp"] == 1'000'000);
    CHECK(j["id"] == 0x100);
    CHECK(j["dlc"] == 8);
    CHECK(j["data"].size() == 8);
}

TEST_CASE("serialize multiplexed signal", "[json][serialize]") {
    auto id = StandardId::create(0x200).value();
    auto dlc = Dlc::create(8).value();

    DbcSignal sig{
        .name = SignalName{"MuxedTemp"},
        .start_bit = BitPosition{16},
        .bit_length = BitLength{8},
        .byte_order = ByteOrder::BigEndian,
        .is_signed = true,
        .factor = RationalFactor{Rational{1, 1}},
        .offset = RationalOffset{Rational{-40, 1}},
        .minimum = RationalBound{Rational{-40, 1}},
        .maximum = RationalBound{Rational{215, 1}},
        .unit = Unit{"C"},
        .presence = Multiplexed{SignalName{"MuxSelector"}, {MultiplexValue{3}}},
    };

    DbcDefinition dbc{
        .version = "",
        .messages = {DbcMessage{
            .id = CanId{id},
            .name = MessageName{"Sensors"},
            .dlc = dlc,
            .sender = NodeName{"ECU2"},
            .signals = {sig},
        }},
    };

    auto str = detail::serialize_parse_dbc(dbc);
    auto j = json::parse(str);
    auto& jsig = j["dbc"]["messages"][0]["signals"][0];

    CHECK(jsig["byteOrder"] == "big_endian");
    CHECK(jsig["signed"] == true);
    CHECK(jsig["multiplexor"] == "MuxSelector");
    CHECK(jsig["multiplex_values"] == json::array({3}));
    CHECK_FALSE(jsig.contains("presence"));
}

TEST_CASE("serialize extended CAN ID in DBC", "[json][serialize]") {
    auto id = ExtendedId::create(0x18FEF100).value();
    auto dlc = Dlc::create(8).value();

    DbcDefinition dbc{
        .version = "",
        .messages = {DbcMessage{
            .id = CanId{id},
            .name = MessageName{"J1939Msg"},
            .dlc = dlc,
            .sender = NodeName{"Truck"},
            .signals = {},
        }},
    };

    auto str = detail::serialize_parse_dbc(dbc);
    auto j = json::parse(str);
    auto& msg = j["dbc"]["messages"][0];

    CHECK(msg["id"] == 0x18FEF100);
    CHECK(msg["extended"] == true);
}

TEST_CASE("serialize metric temporal operators", "[json][serialize]") {
    auto inner = ltl::atomic(ltl::equals(SignalName{"Brake"}, PhysicalValue{Rational{1, 1}}));
    auto formula = ltl::always_within(Timestamp{2'000'000}, std::move(inner));
    std::vector<LtlFormula> props;
    props.push_back(std::move(formula));
    auto str = detail::serialize_set_properties(props);
    auto j = json::parse(str);

    CHECK(j["properties"][0]["operator"] == "metricAlways");
    CHECK(j["properties"][0]["timebound"] == 2'000'000);
}

TEST_CASE("serialize all predicate types", "[json][serialize]") {
    auto check = [](Predicate p, const std::string& expected) {
        auto formula = ltl::atomic(std::move(p));
        std::vector<LtlFormula> props;
        props.push_back(std::move(formula));
        auto str = detail::serialize_set_properties(props);
        auto j = json::parse(str);
        CHECK(j["properties"][0]["predicate"]["predicate"] == expected);
    };

    check(ltl::equals(SignalName{"S"}, PhysicalValue{Rational{}}), "equals");
    check(ltl::less_than(SignalName{"S"}, PhysicalValue{Rational{}}), "lessThan");
    check(ltl::greater_than(SignalName{"S"}, PhysicalValue{Rational{}}), "greaterThan");
    check(ltl::at_most(SignalName{"S"}, PhysicalValue{Rational{}}), "lessThanOrEqual");
    check(ltl::at_least(SignalName{"S"}, PhysicalValue{Rational{}}), "greaterThanOrEqual");
    check(ltl::between(SignalName{"S"}, PhysicalValue{Rational{}}, PhysicalValue{Rational{100, 1}}),
          "between");
    check(ltl::changed_by(SignalName{"S"}, Delta{10.0}), "changedBy");
    check(ltl::stable_within(SignalName{"S"}, Tolerance{2.0}), "stableWithin");
}

// ===========================================================================
// JSON Parsing tests
// ===========================================================================

TEST_CASE("parse_success on success response", "[json][parse]") {
    auto result = detail::parse_success(R"({"status": "success"})");
    CHECK(result.has_value());
}

TEST_CASE("parse_success on error response", "[json][parse]") {
    auto result = detail::parse_success(
        R"({"status": "error", "code": "handler_no_dbc", "message": "DBC not loaded"})");
    CHECK_FALSE(result.has_value());
    CHECK(result.error().kind() == ErrorKind::Protocol);
    CHECK_THAT(std::string{result.error().message()}, ContainsSubstring("DBC not loaded"));
}

TEST_CASE("parse_success rejects \"ack\" status", "[json][parse]") {
    // parse_success is strict: only accepts "success". "ack" is for trace events.
    auto result = detail::parse_success(R"({"status": "ack"})");
    CHECK_FALSE(result.has_value());
    CHECK(result.error().kind() == ErrorKind::Protocol);
    CHECK_THAT(std::string{result.error().message()}, ContainsSubstring("Unexpected status"));
}

TEST_CASE("parse_event_ack on ack response", "[json][parse]") {
    auto result = detail::parse_event_ack(R"({"status": "ack"})");
    CHECK(result.has_value());
}

TEST_CASE("parse_event_ack rejects \"success\" status", "[json][parse]") {
    // Trace events always emit "ack" per Agda Protocol/StreamState.agda;
    // "success" must not be accepted.
    auto result = detail::parse_event_ack(R"({"status": "success"})");
    CHECK_FALSE(result.has_value());
    CHECK(result.error().kind() == ErrorKind::Protocol);
    CHECK_THAT(std::string{result.error().message()}, ContainsSubstring("Unexpected status"));
}

TEST_CASE("parse_event_ack on error response", "[json][parse]") {
    auto result = detail::parse_event_ack(
        R"({"status": "error", "message": "non-monotonic timestamp", "code": "monotonicity_violation"})");
    CHECK_FALSE(result.has_value());
    CHECK(result.error().kind() == ErrorKind::Protocol);
    CHECK_THAT(std::string{result.error().message()}, ContainsSubstring("non-monotonic timestamp"));
}

TEST_CASE("parse_validation response", "[json][parse]") {
    auto result = detail::parse_validation(R"({
        "status": "validation",
        "has_errors": true,
        "issues": [
            {"severity": "error", "code": "factor_zero", "detail": "Signal X has zero factor"},
            {"severity": "warning", "code": "empty_message", "detail": "Message Y is empty"}
        ]
    })");
    REQUIRE(result.has_value());
    CHECK(result->has_errors);
    CHECK(result->issues.size() == 2);
    CHECK(result->issues[0].severity == IssueSeverity::Error);
    CHECK(result->issues[0].code == IssueCode::FactorZero);
    CHECK(result->issues[1].severity == IssueSeverity::Warning);
    CHECK(result->issues[1].code == IssueCode::EmptyMessage);
}

TEST_CASE("parse_extraction response", "[json][parse]") {
    auto result = detail::parse_extraction(R"({
        "status": "success",
        "values": [
            {"name": "Speed", "value": 120.5},
            {"name": "RPM", "value": 3000}
        ],
        "errors": [
            {"name": "BadSig", "error": "overflow"}
        ],
        "absent": ["MuxedTemp"]
    })");
    REQUIRE(result.has_value());
    CHECK(result->values.size() == 2);
    CHECK(result->values[0].name == SignalName{"Speed"});
    CHECK(result->values[0].value == PhysicalValue{Rational{241, 2}});
    CHECK(result->values[1].value == PhysicalValue{Rational{3000, 1}});
    CHECK(result->errors.size() == 1);
    CHECK(result->errors[0].first == SignalName{"BadSig"});
    CHECK(result->absent.size() == 1);
    CHECK(result->absent[0] == SignalName{"MuxedTemp"});
}

TEST_CASE("parse_extraction with rational values", "[json][parse]") {
    auto result = detail::parse_extraction(R"({
        "status": "success",
        "values": [
            {"name": "Ratio", "value": {"numerator": 1, "denominator": 3}}
        ],
        "errors": [],
        "absent": []
    })");
    REQUIRE(result.has_value());
    CHECK(result->values[0].value == PhysicalValue{Rational{1, 3}});
}

TEST_CASE("parse_frame_data response", "[json][parse]") {
    auto result = detail::parse_frame_data(R"({
        "status": "success",
        "data": [232, 3, 0, 0, 0, 0, 0, 0]
    })");
    REQUIRE(result.has_value());
    CHECK(result->size() == 8);
    CHECK((*result)[0] == std::byte{232});
    CHECK((*result)[1] == std::byte{3});
    CHECK((*result)[7] == std::byte{0});
}

TEST_CASE("parse_frame_response ack", "[json][parse]") {
    auto result = detail::parse_frame_response(R"({"status": "ack"})");
    REQUIRE(result.has_value());
    CHECK(std::holds_alternative<Ack>(*result));
}

TEST_CASE("parse_frame_response violation", "[json][parse]") {
    auto result = detail::parse_frame_response(R"({
        "status": "fails",
        "type": "property",
        "property_index": 0,
        "timestamp": 5000000,
        "reason": "Speed exceeded limit"
    })");
    REQUIRE(result.has_value());
    REQUIRE(std::holds_alternative<Violation>(*result));
    auto& v = std::get<Violation>(*result);
    CHECK(v.property_index == PropertyIndex{0});
    CHECK(v.timestamp == Timestamp{5'000'000});
    CHECK(v.reason == "Speed exceeded limit");
}

TEST_CASE("parse_frame_response violation with rational index", "[json][parse]") {
    auto result = detail::parse_frame_response(R"({
        "status": "fails",
        "type": "property",
        "property_index": {"numerator": 2, "denominator": 1},
        "timestamp": {"numerator": 3000000, "denominator": 1}
    })");
    REQUIRE(result.has_value());
    auto& v = std::get<Violation>(*result);
    CHECK(v.property_index == PropertyIndex{2});
    CHECK(v.timestamp == Timestamp{3'000'000});
}

TEST_CASE("parse_stream_result complete", "[json][parse]") {
    auto result = detail::parse_stream_result(R"({
        "status": "complete",
        "results": [
            {"type": "property", "status": "holds", "property_index": 0},
            {"type": "property", "status": "fails", "property_index": 1,
             "timestamp": 5000000, "reason": "Never satisfied"},
            {"type": "property", "status": "unresolved", "property_index": 2,
             "reason": "Atomic: predicate never resolved at end of stream"}
        ]
    })");
    REQUIRE(result.has_value());
    CHECK(result->results.size() == 3);
    CHECK(result->results[0].verdict == Verdict::Holds);
    CHECK(result->results[0].property_index == PropertyIndex{0});
    CHECK(result->results[1].verdict == Verdict::Fails);
    CHECK(result->results[1].timestamp == Timestamp{5'000'000});
    CHECK(result->results[1].reason == "Never satisfied");
    CHECK(result->results[2].verdict == Verdict::Unresolved);
    CHECK(result->results[2].property_index == PropertyIndex{2});
    CHECK(result->results[2].reason == "Atomic: predicate never resolved at end of stream");
}

TEST_CASE("parse_dbc_response", "[json][parse]") {
    auto result = detail::parse_dbc_response(R"({
        "status": "success",
        "dbc": {
            "version": "2.0",
            "messages": [{
                "id": 256,
                "name": "TestMsg",
                "dlc": 8,
                "sender": "Node1",
                "extended": false,
                "signals": [{
                    "name": "Sig1",
                    "startBit": 0,
                    "length": 8,
                    "byteOrder": "little_endian",
                    "signed": false,
                    "factor": 1,
                    "offset": 0,
                    "minimum": 0,
                    "maximum": 255,
                    "unit": ""
                }]
            }]
        }
    })");
    REQUIRE(result.has_value());
    CHECK(result->version == "2.0");
    CHECK(result->messages.size() == 1);
    CHECK(result->messages[0].name == MessageName{"TestMsg"});
    CHECK(result->messages[0].signals[0].name == SignalName{"Sig1"});
    CHECK(result->messages[0].signals[0].factor == RationalFactor{Rational{1, 1}});
}

// ===========================================================================
// JSON parse error + edge-case tests
// ===========================================================================

TEST_CASE("parse_success rejects malformed JSON", "[json][parse][error]") {
    auto result = detail::parse_success("not json at all");
    CHECK_FALSE(result.has_value());
    CHECK(result.error().kind() == ErrorKind::Protocol);
}

TEST_CASE("parse_success rejects missing status field", "[json][parse][error]") {
    auto result = detail::parse_success(R"({"foo": "bar"})");
    CHECK_FALSE(result.has_value());
    CHECK(result.error().kind() == ErrorKind::Protocol);
    CHECK_THAT(std::string{result.error().message()}, ContainsSubstring("Unexpected status"));
}

TEST_CASE("parse_extraction rejects missing status field", "[json][parse][error]") {
    auto result = detail::parse_extraction(R"({"values": []})");
    CHECK_FALSE(result.has_value());
    CHECK(result.error().kind() == ErrorKind::Protocol);
    CHECK_THAT(std::string{result.error().message()}, ContainsSubstring("status"));
}

TEST_CASE("parse_extraction handles missing optional arrays", "[json][parse]") {
    auto result = detail::parse_extraction(R"({"status": "success"})");
    REQUIRE(result.has_value());
    CHECK(result->values.empty());
    CHECK(result->errors.empty());
    CHECK(result->absent.empty());
}

TEST_CASE("parse_frame_data accepts variable-length data", "[json][parse]") {
    auto result = detail::parse_frame_data(R"({"status": "success", "data": [1, 2, 3]})");
    REQUIRE(result.has_value());
    CHECK(result->size() == 3);
    CHECK((*result)[0] == std::byte{1});
    CHECK((*result)[2] == std::byte{3});
}

TEST_CASE("parse_frame_data accepts CAN-FD 64-byte data", "[json][parse]") {
    // DLC 15 → 64 bytes
    std::string json_str = R"({"status": "success", "data": [)";
    for (int i = 0; i < 64; ++i) {
        if (i > 0)
            json_str += ", ";
        json_str += std::to_string(i);
    }
    json_str += "]}";
    auto result = detail::parse_frame_data(json_str);
    REQUIRE(result.has_value());
    CHECK(result->size() == 64);
    CHECK((*result)[0] == std::byte{0});
    CHECK((*result)[63] == std::byte{63});
}

TEST_CASE("parse_frame_response rejects empty status", "[json][parse][error]") {
    auto result = detail::parse_frame_response(R"({"foo": "bar"})");
    CHECK_FALSE(result.has_value());
    CHECK_THAT(std::string{result.error().message()}, ContainsSubstring("Unexpected frame status"));
}

TEST_CASE("parse_dbc_response rejects missing dbc field", "[json][parse][error]") {
    auto result = detail::parse_dbc_response(R"({"status": "success"})");
    CHECK_FALSE(result.has_value());
    CHECK_THAT(std::string{result.error().message()}, ContainsSubstring("dbc"));
}

TEST_CASE("parse_dbc_response rejects malformed signal", "[json][parse][error]") {
    auto result = detail::parse_dbc_response(R"({
        "status": "success",
        "dbc": {
            "version": "1.0",
            "messages": [{
                "id": 256, "name": "Msg", "dlc": 8,
                "signals": [{"MISSING_NAME": true}]
            }]
        }
    })");
    CHECK_FALSE(result.has_value());
    CHECK(result.error().kind() == ErrorKind::Protocol);
}

TEST_CASE("parse_dbc_response with empty messages array", "[json][parse]") {
    auto result = detail::parse_dbc_response(R"({
        "status": "success",
        "dbc": {"version": "1.0", "messages": []}
    })");
    REQUIRE(result.has_value());
    CHECK(result->messages.empty());
    CHECK(result->version == "1.0");
}

TEST_CASE("parse_dbc_response with empty signals array", "[json][parse]") {
    auto result = detail::parse_dbc_response(R"({
        "status": "success",
        "dbc": {
            "version": "",
            "messages": [{
                "id": 256, "name": "EmptyMsg", "dlc": 8,
                "extended": false, "signals": []
            }]
        }
    })");
    REQUIRE(result.has_value());
    CHECK(result->messages.size() == 1);
    CHECK(result->messages[0].signals.empty());
}

TEST_CASE("parse_validation with unknown issue code returns Unknown", "[json][parse]") {
    auto result = detail::parse_validation(R"({
        "status": "validation",
        "has_errors": true,
        "issues": [
            {"severity": "error", "code": "some_future_code", "detail": "New check"}
        ]
    })");
    REQUIRE(result.has_value());
    CHECK(result->issues[0].code == IssueCode::Unknown);
}

TEST_CASE("parse_validation rejects unknown severity string", "[json][parse][error]") {
    auto result = detail::parse_validation(R"({
        "status": "validation",
        "has_errors": false,
        "issues": [
            {"severity": "info", "code": "empty_message", "detail": "x"}
        ]
    })");
    REQUIRE_FALSE(result.has_value());
    CHECK(result.error().kind() == ErrorKind::Protocol);
    CHECK_THAT(std::string{result.error().message()}, ContainsSubstring("severity"));
}

TEST_CASE("parse_validation rejects missing severity string", "[json][parse][error]") {
    auto result = detail::parse_validation(R"({
        "status": "validation",
        "has_errors": false,
        "issues": [
            {"code": "empty_message", "detail": "x"}
        ]
    })");
    REQUIRE_FALSE(result.has_value());
    CHECK(result.error().kind() == ErrorKind::Protocol);
}

TEST_CASE("parse_number rejects non-numeric JSON via exception", "[json][parse][error]") {
    // parse_number throws on bad input; the public wrapper converts to Result
    auto result = detail::parse_extraction(R"({
        "status": "success",
        "values": [{"name": "Bad", "value": "not_a_number"}]
    })");
    CHECK_FALSE(result.has_value());
    CHECK(result.error().kind() == ErrorKind::Protocol);
}

TEST_CASE("parse_dbc_response rejects out-of-range CAN ID", "[json][parse][error]") {
    auto result = detail::parse_dbc_response(R"({
        "status": "success",
        "dbc": {
            "version": "",
            "messages": [{
                "id": 99999, "name": "Bad", "dlc": 8,
                "extended": false, "signals": []
            }]
        }
    })");
    CHECK_FALSE(result.has_value());
    CHECK_THAT(std::string{result.error().message()}, ContainsSubstring("CAN ID"));
}

TEST_CASE("parse_dbc_response rejects out-of-range DLC", "[json][parse][error]") {
    auto result = detail::parse_dbc_response(R"({
        "status": "success",
        "dbc": {
            "version": "",
            "messages": [{
                "id": 256, "name": "Bad", "dlc": 99,
                "extended": false, "signals": []
            }]
        }
    })");
    CHECK_FALSE(result.has_value());
    CHECK_THAT(std::string{result.error().message()}, ContainsSubstring("DLC"));
}

// ===========================================================================
// Tier 1 DBC metadata round-trip (Phase B.1)
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

    auto str = detail::serialize_parse_dbc(dbc);
    auto j = json::parse(str);

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
    auto dbc = make_test_dbc();
    auto str = detail::serialize_parse_dbc(dbc);
    auto j = json::parse(str);
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
    auto result = detail::parse_dbc_response(R"({
        "status": "success",
        "dbc": {
            "version": "1.0",
            "messages": [],
            "environmentVars": [
                {"name": "Bad", "varType": 7,
                 "initial": 0, "minimum": 0, "maximum": 0}
            ]
        }
    })");
    CHECK_FALSE(result.has_value());
    CHECK(result.error().kind() == ErrorKind::Protocol);
    CHECK_THAT(std::string{result.error().message()},
               ContainsSubstring("environment variable type"));
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
    const auto& ev = result->environment_vars[0];
    CHECK(ev.initial == Rational{1, 10});
    CHECK(ev.minimum == Rational{-1, 3});
    CHECK(ev.maximum == Rational{22, 7});
}

// ===========================================================================
// Tier 2 DBC metadata round-trip (Phase B.1.x) — nodes, comments, attributes
// ===========================================================================

TEST_CASE("Tier 2 DBC metadata round-trips through serialize + parse",
          "[json][serialize][parse][dbc][tier2]") {
    auto dbc = make_test_dbc();
    dbc.nodes.push_back(DbcNode{.name = "ECU1"});
    dbc.nodes.push_back(DbcNode{.name = "Gateway"});

    dbc.comments.push_back(DbcComment{
        .target = DbcCommentTargetNetwork{},
        .text = "Vehicle network",
    });
    dbc.comments.push_back(DbcComment{
        .target = DbcCommentTargetNode{.node = "ECU1"},
        .text = "Engine control unit",
    });
    dbc.comments.push_back(DbcComment{
        .target = DbcCommentTargetMessage{.id = 256, .extended = false},
        .text = "Engine status message",
    });
    dbc.comments.push_back(DbcComment{
        .target = DbcCommentTargetSignal{.id = 512, .extended = true, .signal = "Torque"},
        .text = "Requested torque",
    });
    dbc.comments.push_back(DbcComment{
        .target = DbcCommentTargetEnvVar{.env_var = "AmbientTemp"},
        .text = "Ambient temperature sensor",
    });

    dbc.attributes.push_back(DbcAttrDef{
        .name = "GenMsgCycleTime",
        .scope = DbcAttrScope::Message,
        .attr_type = DbcAttrTypeInt{.min = 0, .max = 10000},
    });
    dbc.attributes.push_back(DbcAttrDef{
        .name = "SignalGain",
        .scope = DbcAttrScope::Signal,
        .attr_type = DbcAttrTypeFloat{.min = Rational{-1, 2}, .max = Rational{22, 7}},
    });
    dbc.attributes.push_back(DbcAttrDef{
        .name = "BusName",
        .scope = DbcAttrScope::Network,
        .attr_type = DbcAttrTypeString{},
    });
    dbc.attributes.push_back(DbcAttrDef{
        .name = "ModuleType",
        .scope = DbcAttrScope::Node,
        .attr_type = DbcAttrTypeEnum{.values = {"ECU", "Gateway", "Sensor"}},
    });
    dbc.attributes.push_back(DbcAttrDef{
        .name = "AddressMask",
        .scope = DbcAttrScope::Message,
        .attr_type = DbcAttrTypeHex{.min = 0, .max = 65535},
    });
    dbc.attributes.push_back(DbcAttrDefault{
        .name = "GenMsgCycleTime",
        .value = DbcAttrValueInt{.value = 100},
    });
    dbc.attributes.push_back(DbcAttrAssign{
        .name = "GenMsgCycleTime",
        .target = DbcAttrTargetMessage{.id = 256, .extended = false},
        .value = DbcAttrValueInt{.value = 20},
    });
    dbc.attributes.push_back(DbcAttrAssign{
        .name = "SignalGain",
        .target = DbcAttrTargetSignal{.id = 512, .extended = true, .signal = "Torque"},
        .value = DbcAttrValueFloat{.value = Rational{3, 4}},
    });
    dbc.attributes.push_back(DbcAttrAssign{
        .name = "ModuleType",
        .target = DbcAttrTargetNode{.node = "ECU1"},
        .value = DbcAttrValueEnum{.value = 0},
    });
    dbc.attributes.push_back(DbcAttrAssign{
        .name = "SenderRole",
        .target = DbcAttrTargetNodeMsg{.node = "ECU1", .id = 256, .extended = false},
        .value = DbcAttrValueString{.value = "producer"},
    });
    dbc.attributes.push_back(DbcAttrAssign{
        .name = "SignalAccess",
        .target =
            DbcAttrTargetNodeSig{.node = "ECU1", .id = 512, .extended = true, .signal = "Torque"},
        .value = DbcAttrValueHex{.value = 255},
    });

    auto str = detail::serialize_parse_dbc(dbc);
    auto j = json::parse(str);

    // Confirm wire shape: every tagged union carries "kind" first.
    REQUIRE(j["dbc"]["nodes"].is_array());
    REQUIRE(j["dbc"]["nodes"].size() == 2);
    CHECK(j["dbc"]["nodes"][0]["name"] == "ECU1");

    REQUIRE(j["dbc"]["comments"].size() == 5);
    CHECK(j["dbc"]["comments"][0]["target"]["kind"] == "network");
    CHECK(j["dbc"]["comments"][3]["target"]["kind"] == "signal");
    CHECK(j["dbc"]["comments"][3]["target"]["extended"] == true);

    REQUIRE(j["dbc"]["attributes"].size() == 11);
    CHECK(j["dbc"]["attributes"][0]["kind"] == "definition");
    CHECK(j["dbc"]["attributes"][0]["attrType"]["kind"] == "int");
    // Float attribute values serialize as {numerator, denominator} dicts
    // — matches Python's Fraction, drifts under double.
    CHECK(j["dbc"]["attributes"][1]["attrType"]["min"]["numerator"] == -1);
    CHECK(j["dbc"]["attributes"][1]["attrType"]["min"]["denominator"] == 2);

    // Route the serialized JSON through parse_dbc_response (wrap as success
    // envelope) to exercise the parser leg of the round-trip.
    json envelope = {{"status", "success"}, {"dbc", j["dbc"]}};
    auto result = detail::parse_dbc_response(envelope.dump());
    REQUIRE(result.has_value());

    REQUIRE(result->nodes.size() == 2);
    CHECK(result->nodes[0].name == "ECU1");
    CHECK(result->nodes[1].name == "Gateway");

    REQUIRE(result->comments.size() == 5);
    CHECK(std::holds_alternative<DbcCommentTargetNetwork>(result->comments[0].target));
    CHECK(std::get<DbcCommentTargetNode>(result->comments[1].target).node == "ECU1");
    const auto& msg_ct = std::get<DbcCommentTargetMessage>(result->comments[2].target);
    CHECK(msg_ct.id == 256);
    CHECK_FALSE(msg_ct.extended);
    const auto& sig_ct = std::get<DbcCommentTargetSignal>(result->comments[3].target);
    CHECK(sig_ct.id == 512);
    CHECK(sig_ct.extended);
    CHECK(sig_ct.signal == "Torque");
    CHECK(std::get<DbcCommentTargetEnvVar>(result->comments[4].target).env_var == "AmbientTemp");

    REQUIRE(result->attributes.size() == 11);
    // Definitions
    const auto& def_int = std::get<DbcAttrDef>(result->attributes[0]);
    CHECK(def_int.name == "GenMsgCycleTime");
    CHECK(def_int.scope == DbcAttrScope::Message);
    CHECK(std::get<DbcAttrTypeInt>(def_int.attr_type).max == 10000);
    const auto& def_float = std::get<DbcAttrDef>(result->attributes[1]);
    const auto& float_bounds = std::get<DbcAttrTypeFloat>(def_float.attr_type);
    CHECK(float_bounds.min == Rational{-1, 2});
    CHECK(float_bounds.max == Rational{22, 7});
    const auto& def_enum = std::get<DbcAttrDef>(result->attributes[3]);
    const auto& enum_labels = std::get<DbcAttrTypeEnum>(def_enum.attr_type);
    REQUIRE(enum_labels.values.size() == 3);
    CHECK(enum_labels.values[1] == "Gateway");

    // Default
    const auto& dflt = std::get<DbcAttrDefault>(result->attributes[5]);
    CHECK(dflt.name == "GenMsgCycleTime");
    CHECK(std::get<DbcAttrValueInt>(dflt.value).value == 100);

    // Assignments (target + value parity)
    const auto& assign_sig = std::get<DbcAttrAssign>(result->attributes[7]);
    const auto& sig_tgt = std::get<DbcAttrTargetSignal>(assign_sig.target);
    CHECK(sig_tgt.id == 512);
    CHECK(sig_tgt.extended);
    CHECK(sig_tgt.signal == "Torque");
    CHECK(std::get<DbcAttrValueFloat>(assign_sig.value).value == Rational{3, 4});

    const auto& assign_nm = std::get<DbcAttrAssign>(result->attributes[9]);
    const auto& nm_tgt = std::get<DbcAttrTargetNodeMsg>(assign_nm.target);
    CHECK(nm_tgt.node == "ECU1");
    CHECK(nm_tgt.id == 256);
    CHECK_FALSE(nm_tgt.extended);

    const auto& assign_ns = std::get<DbcAttrAssign>(result->attributes[10]);
    const auto& ns_tgt = std::get<DbcAttrTargetNodeSig>(assign_ns.target);
    CHECK(ns_tgt.node == "ECU1");
    CHECK(ns_tgt.signal == "Torque");
    CHECK(ns_tgt.extended);
    CHECK(std::get<DbcAttrValueHex>(assign_ns.value).value == 255);
}

TEST_CASE("DbcSignal.receivers round-trips through serialize + parse",
          "[json][serialize][parse][dbc][tier2]") {
    auto dbc = make_test_dbc();
    REQUIRE(dbc.messages.size() == 1);
    REQUIRE(dbc.messages[0].signals.size() == 1);
    dbc.messages[0].signals[0].receivers = {"ECU_A", "ECU_B"};

    auto str = detail::serialize_parse_dbc(dbc);
    auto j = json::parse(str);

    REQUIRE(j["dbc"]["messages"][0]["signals"][0]["receivers"].is_array());
    CHECK(j["dbc"]["messages"][0]["signals"][0]["receivers"].size() == 2);
    CHECK(j["dbc"]["messages"][0]["signals"][0]["receivers"][0] == "ECU_A");
    CHECK(j["dbc"]["messages"][0]["signals"][0]["receivers"][1] == "ECU_B");

    json envelope = {{"status", "success"}, {"dbc", j["dbc"]}};
    auto result = detail::parse_dbc_response(envelope.dump());
    REQUIRE(result.has_value());
    REQUIRE(result->messages.size() == 1);
    REQUIRE(result->messages[0].signals.size() == 1);
    const auto& parsed = result->messages[0].signals[0].receivers;
    REQUIRE(parsed.size() == 2);
    CHECK(parsed[0] == "ECU_A");
    CHECK(parsed[1] == "ECU_B");
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
                "unit": ""
            }]
        }]}
    })");
    REQUIRE(result.has_value());
    REQUIRE(result->messages.size() == 1);
    REQUIRE(result->messages[0].signals.size() == 1);
    CHECK(result->messages[0].signals[0].receivers.empty());
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

TEST_CASE("parse_extraction rejects zero denominator in rational", "[json][parse][error]") {
    auto result = detail::parse_extraction(R"({
        "status": "success",
        "values": [{"name": "Bad", "value": {"numerator": 1, "denominator": 0}}],
        "errors": [], "absent": []
    })");
    CHECK_FALSE(result.has_value());
    CHECK_THAT(std::string{result.error().message()}, ContainsSubstring("denominator"));
}

TEST_CASE("parse_frame_response rejects zero denominator in timestamp", "[json][parse][error]") {
    auto result = detail::parse_frame_response(R"({
        "status": "fails",
        "type": "property",
        "property_index": 0,
        "timestamp": {"numerator": 1000, "denominator": 0}
    })");
    CHECK_FALSE(result.has_value());
    CHECK_THAT(std::string{result.error().message()}, ContainsSubstring("denominator"));
}

TEST_CASE("parse_stream_result rejects malformed JSON", "[json][parse][error]") {
    auto result = detail::parse_stream_result("not json");
    CHECK_FALSE(result.has_value());
    CHECK(result.error().kind() == ErrorKind::Protocol);
}

TEST_CASE("parse_stream_result rejects missing results field", "[json][parse][error]") {
    auto result = detail::parse_stream_result(R"({"status": "complete"})");
    CHECK_FALSE(result.has_value());
    CHECK(result.error().kind() == ErrorKind::Protocol);
}

TEST_CASE("parse_frame_response rejects negative property_index", "[json][parse][error]") {
    auto result = detail::parse_frame_response(R"({
        "status": "fails",
        "type": "property",
        "property_index": -1,
        "timestamp": 100
    })");
    CHECK_FALSE(result.has_value());
    CHECK(result.error().kind() == ErrorKind::Protocol);
    CHECK_THAT(std::string{result.error().message()}, ContainsSubstring("Negative property_index"));
}

TEST_CASE("parse_stream_result rejects negative property_index", "[json][parse][error]") {
    auto result = detail::parse_stream_result(R"({
        "status": "complete",
        "results": [{"status": "holds", "property_index": -5}]
    })");
    CHECK_FALSE(result.has_value());
    CHECK(result.error().kind() == ErrorKind::Protocol);
    CHECK_THAT(std::string{result.error().message()}, ContainsSubstring("Negative property_index"));
}

TEST_CASE("parse_frame_response rejects fails with missing timestamp", "[json][parse][error]") {
    auto result = detail::parse_frame_response(R"({
        "status": "fails",
        "type": "property",
        "property_index": 0
    })");
    CHECK_FALSE(result.has_value());
    CHECK(result.error().kind() == ErrorKind::Protocol);
}

TEST_CASE("parse_frame_response rejects fails with missing property_index",
          "[json][parse][error]") {
    auto result = detail::parse_frame_response(R"({
        "status": "fails",
        "type": "property",
        "timestamp": 100
    })");
    CHECK_FALSE(result.has_value());
    CHECK(result.error().kind() == ErrorKind::Protocol);
}

TEST_CASE("parse_stream_result rejects entry with missing status", "[json][parse][error]") {
    auto result = detail::parse_stream_result(R"({
        "status": "complete",
        "results": [{"property_index": 0}]
    })");
    CHECK_FALSE(result.has_value());
    CHECK(result.error().kind() == ErrorKind::Protocol);
    CHECK_THAT(std::string{result.error().message()}, ContainsSubstring("Unknown verdict status"));
}

TEST_CASE("parse_rational_as_int rejects non-exact rational", "[json][parse][error]") {
    // {"numerator": 3, "denominator": 2} → 1.5, not an integer
    auto result = detail::parse_frame_response(R"({
        "status": "fails",
        "type": "property",
        "property_index": {"numerator": 3, "denominator": 2},
        "timestamp": 100
    })");
    CHECK_FALSE(result.has_value());
    CHECK(result.error().kind() == ErrorKind::Protocol);
    CHECK_THAT(std::string{result.error().message()}, ContainsSubstring("Non-exact rational"));
}

TEST_CASE("parse_frame_response rejects fails without type property", "[json][parse][error]") {
    auto result = detail::parse_frame_response(R"({
        "status": "fails",
        "property_index": 0,
        "timestamp": 100
    })");
    CHECK_FALSE(result.has_value());
    CHECK(result.error().kind() == ErrorKind::Protocol);
    CHECK_THAT(std::string{result.error().message()},
               ContainsSubstring("Expected type \"property\""));
}

TEST_CASE("parse_rational rejects float input", "[json][parse][error]") {
    // A floating-point 1.5 should be rejected (not integer, not {num, den} dict)
    auto result = detail::parse_dbc_response(R"({
        "status": "success",
        "dbc": {
            "version": "", "messages": [{
                "id": 1, "name": "M", "dlc": 8, "extended": false,
                "signals": [{
                    "name": "S", "startBit": 0, "length": 8,
                    "byteOrder": "little_endian", "signed": false,
                    "factor": 1.5, "offset": 0, "minimum": 0,
                    "maximum": 255, "unit": ""
                }]
            }]
        }
    })");
    CHECK_FALSE(result.has_value());
    CHECK(result.error().kind() == ErrorKind::Protocol);
}

TEST_CASE("parse_dbc_response accepts standard CAN ID at boundary (2047)", "[json][parse]") {
    auto result = detail::parse_dbc_response(R"({
        "status": "success",
        "dbc": {
            "version": "", "messages": [{
                "id": 2047, "name": "Max", "dlc": 8,
                "extended": false, "signals": []
            }]
        }
    })");
    REQUIRE(result.has_value());
    auto& id = result->messages[0].id;
    CHECK(std::get<StandardId>(id).value() == 2047);
}

TEST_CASE("parse_dbc_response rejects standard CAN ID at boundary (2048)", "[json][parse][error]") {
    auto result = detail::parse_dbc_response(R"({
        "status": "success",
        "dbc": {
            "version": "", "messages": [{
                "id": 2048, "name": "Bad", "dlc": 8,
                "extended": false, "signals": []
            }]
        }
    })");
    CHECK_FALSE(result.has_value());
    CHECK_THAT(std::string{result.error().message()}, ContainsSubstring("CAN ID"));
}

TEST_CASE("parse_dbc_response rejects truncating standard CAN ID (70000)", "[json][parse][error]") {
    auto result = detail::parse_dbc_response(R"({
        "status": "success",
        "dbc": {
            "version": "", "messages": [{
                "id": 70000, "name": "Bad", "dlc": 8,
                "extended": false, "signals": []
            }]
        }
    })");
    CHECK_FALSE(result.has_value());
    CHECK_THAT(std::string{result.error().message()}, ContainsSubstring("uint16"));
}

TEST_CASE("ExtractionResult::get helper", "[response]") {
    ExtractionResult result{
        .values =
            {
                {SignalName{"Speed"}, PhysicalValue{Rational{120, 1}}},
                {SignalName{"RPM"}, PhysicalValue{Rational{3000, 1}}},
            },
        .errors = {},
        .absent = {},
    };

    CHECK(result.get(SignalName{"Speed"}) == PhysicalValue{Rational{120, 1}});
    CHECK(result.get(SignalName{"RPM"}) == PhysicalValue{Rational{3000, 1}});
    CHECK(result.get(SignalName{"Missing"}) == PhysicalValue{Rational{}});
    CHECK(result.get(SignalName{"Missing"}, PhysicalValue{Rational{-1, 1}}) ==
          PhysicalValue{Rational{-1, 1}});
    CHECK_FALSE(result.has_errors());
}

// ===========================================================================
// Formula pretty-printer tests (format_formula)
// ===========================================================================

TEST_CASE("format_formula always less than", "[enrich]") {
    auto f = ltl::always(
        ltl::atomic(ltl::less_than(SignalName{"Speed"}, PhysicalValue{Rational{220, 1}})));
    CHECK(format_formula(f) == "always(Speed < 220)");
}

TEST_CASE("format_formula never pattern", "[enrich]") {
    auto f = ltl::never(ltl::greater_than(SignalName{"Speed"}, PhysicalValue{Rational{100, 1}}));
    CHECK(format_formula(f) == "never Speed > 100");
}

TEST_CASE("format_formula eventually", "[enrich]") {
    auto f = ltl::eventually(
        ltl::atomic(ltl::equals(SignalName{"Mode"}, PhysicalValue{Rational{1, 1}})));
    CHECK(format_formula(f) == "eventually(Mode = 1)");
}

TEST_CASE("format_formula metric always", "[enrich]") {
    auto f = ltl::always_within(
        Timestamp{5'000'000},
        ltl::atomic(ltl::less_than(SignalName{"Speed"}, PhysicalValue{Rational{220, 1}})));
    CHECK(format_formula(f) == "always within 5s (Speed < 220)");
}

TEST_CASE("format_formula metric eventually", "[enrich]") {
    auto f =
        ltl::within(Timestamp{2'000'000},
                    ltl::atomic(ltl::equals(SignalName{"Mode"}, PhysicalValue{Rational{1, 1}})));
    CHECK(format_formula(f) == "eventually within 2s (Mode = 1)");
}

TEST_CASE("format_formula next", "[enrich]") {
    auto f = ltl::next(
        ltl::atomic(ltl::less_than(SignalName{"Speed"}, PhysicalValue{Rational{220, 1}})));
    CHECK(format_formula(f) == "next(Speed < 220)");
}

TEST_CASE("format_formula and", "[enrich]") {
    auto f = ltl::both(
        ltl::atomic(ltl::less_than(SignalName{"Speed"}, PhysicalValue{Rational{220, 1}})),
        ltl::atomic(ltl::greater_than(SignalName{"RPM"}, PhysicalValue{Rational{500, 1}})));
    CHECK(format_formula(f) == "Speed < 220 and RPM > 500");
}

TEST_CASE("format_formula or", "[enrich]") {
    auto f = ltl::either(
        ltl::atomic(ltl::less_than(SignalName{"Speed"}, PhysicalValue{Rational{220, 1}})),
        ltl::atomic(ltl::greater_than(SignalName{"RPM"}, PhysicalValue{Rational{500, 1}})));
    CHECK(format_formula(f) == "Speed < 220 or RPM > 500");
}

TEST_CASE("format_formula until", "[enrich]") {
    auto f =
        ltl::until(ltl::atomic(ltl::less_than(SignalName{"Speed"}, PhysicalValue{Rational{50, 1}})),
                   ltl::atomic(ltl::equals(SignalName{"Brake"}, PhysicalValue{Rational{1, 1}})));
    CHECK(format_formula(f) == "Speed < 50 until Brake = 1");
}

TEST_CASE("format_formula release", "[enrich]") {
    auto f = ltl::release(ltl::atomic(ltl::equals(SignalName{"A"}, PhysicalValue{Rational{1, 1}})),
                          ltl::atomic(ltl::equals(SignalName{"B"}, PhysicalValue{Rational{}})));
    CHECK(format_formula(f) == "A = 1 release B = 0");
}

TEST_CASE("format_formula all predicate types", "[enrich]") {
    auto eq = ltl::atomic(ltl::equals(SignalName{"S"}, PhysicalValue{Rational{42, 1}}));
    CHECK(format_formula(eq) == "S = 42");

    auto lt = ltl::atomic(ltl::less_than(SignalName{"S"}, PhysicalValue{Rational{10, 1}}));
    CHECK(format_formula(lt) == "S < 10");

    auto gt = ltl::atomic(ltl::greater_than(SignalName{"S"}, PhysicalValue{Rational{5, 1}}));
    CHECK(format_formula(gt) == "S > 5");

    auto le = ltl::atomic(ltl::at_most(SignalName{"S"}, PhysicalValue{Rational{100, 1}}));
    CHECK(format_formula(le) == "S <= 100");

    auto ge = ltl::atomic(ltl::at_least(SignalName{"S"}, PhysicalValue{Rational{}}));
    CHECK(format_formula(ge) == "S >= 0");

    auto bw = ltl::atomic(ltl::between(SignalName{"S"}, PhysicalValue{Rational{10, 1}},
                                       PhysicalValue{Rational{29, 2}}));
    CHECK(format_formula(bw) == "10 <= S <= 14.5");

    auto cb = ltl::atomic(ltl::changed_by(SignalName{"S"}, Delta{5.0}));
    CHECK(format_formula(cb) == "\xce\x94S >= 5");

    auto cb_neg = ltl::atomic(ltl::changed_by(SignalName{"S"}, Delta{-3.0}));
    CHECK(format_formula(cb_neg) == "\xce\x94S <= -3");

    auto sw = ltl::atomic(ltl::stable_within(SignalName{"S"}, Tolerance{2.0}));
    CHECK(format_formula(sw) == "|\xce\x94S| <= 2");
}

TEST_CASE("format_formula metric until", "[enrich]") {
    using namespace std::chrono_literals;
    auto f = LtlFormula{MetricUntil{.bound = Timestamp{3'000'000},
                                    .left = std::make_unique<LtlFormula>(ltl::atomic(ltl::less_than(
                                        SignalName{"Speed"}, PhysicalValue{Rational{50, 1}}))),
                                    .right = std::make_unique<LtlFormula>(ltl::atomic(ltl::equals(
                                        SignalName{"Brake"}, PhysicalValue{Rational{1, 1}})))}};
    CHECK(format_formula(f) == "Speed < 50 until within 3s Brake = 1");
}

TEST_CASE("format_formula metric release", "[enrich]") {
    using namespace std::chrono_literals;
    auto f = LtlFormula{
        MetricRelease{.bound = Timestamp{500'000},
                      .left = std::make_unique<LtlFormula>(
                          ltl::atomic(ltl::equals(SignalName{"A"}, PhysicalValue{Rational{1, 1}}))),
                      .right = std::make_unique<LtlFormula>(
                          ltl::atomic(ltl::equals(SignalName{"B"}, PhysicalValue{Rational{}})))}};
    CHECK(format_formula(f) == "A = 1 release within 500ms B = 0");
}
