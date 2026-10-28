// SPDX-FileCopyrightText: 2025 Nicolas Pelletier
// SPDX-License-Identifier: BSD-2-Clause
// Unit tests: JSON serialize/parse.
//
// Covers detail::serialize_* and detail::parse_* for commands, responses,
// DBC trees, frame payloads, and LTL formulas.
#include "test_helpers.hpp"

#include <catch2/catch_test_macros.hpp>
#include <catch2/generators/catch_generators.hpp>
#include <catch2/matchers/catch_matchers.hpp>
#include <catch2/matchers/catch_matchers_string.hpp>

#include "detail/json.hpp"
#include "required.hpp"
#include <aletheia/aletheia.hpp>

#include <nlohmann/json.hpp>

#include <cstddef>
#include <string>
#include <utility>
#include <variant>
#include <vector>

using aletheia::test::required;

using namespace aletheia;
using Json = nlohmann::json;
using aletheia::test::make_test_dbc;
using Catch::Matchers::ContainsSubstring;

// ===========================================================================
// JSON Serialization tests
// ===========================================================================

TEST_CASE("serialize_parse_dbc produces valid JSON", "[json][serialize]") {
    auto const dbc = make_test_dbc();
    auto const str = required(detail::serialize_parse_dbc(dbc));
    auto j = Json::parse(str);

    CHECK(j["type"] == "command");
    CHECK(j["command"] == "parseDBC");
    CHECK(j["dbc"]["version"] == "1.0");
    CHECK(j["dbc"]["messages"].size() == 1);

    auto& msg = j["dbc"]["messages"][0];
    CHECK(msg["id"] == 0x100);
    CHECK(msg["name"] == "VehicleSpeed");
    CHECK(msg["dlc"] == 8);
    CHECK(msg["sender"] == "ECU1");
    // "extended" is omitted on standard 11-bit frames (Agda wire convention).
    CHECK_FALSE(msg.contains("extended"));

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
    // Always-present signals carry the explicit "presence": "always".
    CHECK(sig["presence"] == "always");
}

TEST_CASE("serialize_set_properties produces correct JSON", "[json][serialize]") {
    auto formula = ltl::always(
        ltl::atomic(ltl::less_than(SignalName{"Speed"}, PhysicalValue{Rational{220, 1}})));
    std::vector<LtlFormula> props;
    props.push_back(std::move(formula));
    auto const str = required(detail::serialize_set_properties(props));
    auto j = Json::parse(str);

    CHECK(j["command"] == "setProperties");
    CHECK(j["properties"].size() == 1);
    CHECK(j["properties"][0]["operator"] == "always");
    CHECK(j["properties"][0]["formula"]["operator"] == "atomic");
    CHECK(j["properties"][0]["formula"]["predicate"]["predicate"] == "lessThan");
    CHECK(j["properties"][0]["formula"]["predicate"]["signal"] == "Speed");
    // The wire carries a whole threshold as an integer, and the float principle
    // means it is compared as one: an approximate comparison would read it
    // through a double.
    CHECK(j["properties"][0]["formula"]["predicate"]["value"] == 220);
}

TEST_CASE("serialize multiplexed signal", "[json][serialize]") {
    auto const id = StandardId::create(0x200).value();
    auto const dlc = Dlc::create(8).value();

    DbcSignal const sig{
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
        .presence = Multiplexed{.multiplexor = SignalName{"MuxSelector"},
                                .multiplex_values = {MultiplexValue{3}}},
    };

    DbcDefinition const dbc{
        .version = "",
        .messages = {DbcMessage{
            .id = CanId{id},
            .name = MessageName{"Sensors"},
            .dlc = dlc,
            .sender = NodeName{"ECU2"},
            .signals = {sig},
        }},
    };

    auto const str = required(detail::serialize_parse_dbc(dbc));
    auto j = Json::parse(str);
    auto& jsig = j["dbc"]["messages"][0]["signals"][0];

    CHECK(jsig["byteOrder"] == "big_endian");
    CHECK(jsig["signed"] == true);
    CHECK(jsig["multiplexor"] == "MuxSelector");
    CHECK(jsig["multiplex_values"] == Json::array({3}));
    // Multiplexed signals carry an explicit ``"presence": "multiplexed"``
    // discriminator (cross-binding parity with Agda Formatter, Go
    // ``serializeDBC``, and Python).
    CHECK(jsig["presence"] == "multiplexed");
}

TEST_CASE("serialize extended CAN ID in DBC", "[json][serialize]") {
    auto const id = ExtendedId::create(0x18FEF100).value();
    auto const dlc = Dlc::create(8).value();

    DbcDefinition const dbc{
        .version = "",
        .messages = {DbcMessage{
            .id = CanId{id},
            .name = MessageName{"J1939Msg"},
            .dlc = dlc,
            .sender = NodeName{"Truck"},
            .signals = {},
        }},
    };

    auto const str = required(detail::serialize_parse_dbc(dbc));
    auto j = Json::parse(str);
    auto& msg = j["dbc"]["messages"][0];

    CHECK(msg["id"] == 0x18FEF100);
    CHECK(msg["extended"] == true);
}

TEST_CASE("serialize metric temporal operators", "[json][serialize]") {
    auto inner = ltl::atomic(ltl::equals(SignalName{"Brake"}, PhysicalValue{Rational{1, 1}}));
    auto formula = ltl::always_within(Timestamp{2'000'000}, std::move(inner));
    std::vector<LtlFormula> props;
    props.push_back(std::move(formula));
    auto const str = required(detail::serialize_set_properties(props));
    auto j = Json::parse(str);

    CHECK(j["properties"][0]["operator"] == "metricAlways");
    CHECK(j["properties"][0]["timebound"] == 2'000'000);
}

TEST_CASE("serialize all predicate types", "[json][serialize]") {
    auto const check = [](Predicate p, std::string const& expected) {
        auto formula = ltl::atomic(std::move(p));
        std::vector<LtlFormula> props;
        props.push_back(std::move(formula));
        auto const str = required(detail::serialize_set_properties(props));
        auto j = Json::parse(str);
        CHECK(j["properties"][0]["predicate"]["predicate"] == expected);
    };

    check(ltl::equals(SignalName{"S"}, PhysicalValue{Rational{}}), "equals");
    check(ltl::less_than(SignalName{"S"}, PhysicalValue{Rational{}}), "lessThan");
    check(ltl::greater_than(SignalName{"S"}, PhysicalValue{Rational{}}), "greaterThan");
    check(ltl::less_than_or_equal(SignalName{"S"}, PhysicalValue{Rational{}}), "lessThanOrEqual");
    check(ltl::greater_than_or_equal(SignalName{"S"}, PhysicalValue{Rational{}}),
          "greaterThanOrEqual");
    check(ltl::between(SignalName{"S"}, PhysicalValue{Rational{}}, PhysicalValue{Rational{100, 1}}),
          "between");
    check(ltl::changed_by(SignalName{"S"}, Delta{Rational{10, 1}}), "changedBy");
    check(ltl::stable_within(SignalName{"S"}, Tolerance{Rational{2, 1}}), "stableWithin");
}

// ===========================================================================
// JSON Parsing tests
// ===========================================================================

TEST_CASE("parse_success on success response", "[json][parse]") {
    auto const result = detail::parse_success(R"({"status": "success"})");
    CHECK(result.has_value());
}

TEST_CASE("parse_success on error response", "[json][parse]") {
    auto const result = detail::parse_success(
        R"({"status": "error", "code": "handler_no_dbc", "message": "DBC not loaded"})");
    CHECK_FALSE(result.has_value());
    CHECK(result.error().kind() == ErrorKind::Protocol);
    CHECK_THAT(std::string{result.error().message()}, ContainsSubstring("DBC not loaded"));
}

TEST_CASE("parse_success rejects \"ack\" status", "[json][parse]") {
    // parse_success is strict: only accepts "success". "ack" is for trace events.
    auto const result = detail::parse_success(R"({"status": "ack"})");
    CHECK_FALSE(result.has_value());
    CHECK(result.error().kind() == ErrorKind::Protocol);
    CHECK_THAT(std::string{result.error().message()}, ContainsSubstring("Unexpected status"));
}

TEST_CASE("parse_event_ack on ack response", "[json][parse]") {
    auto const result = detail::parse_event_ack(R"({"status": "ack"})");
    CHECK(result.has_value());
}

TEST_CASE("parse_event_ack rejects \"success\" status", "[json][parse]") {
    // Trace events always emit "ack" per Agda Protocol/StreamState.agda;
    // "success" must not be accepted.
    auto const result = detail::parse_event_ack(R"({"status": "success"})");
    CHECK_FALSE(result.has_value());
    CHECK(result.error().kind() == ErrorKind::Protocol);
    CHECK_THAT(std::string{result.error().message()}, ContainsSubstring("Unexpected status"));
}

TEST_CASE("parse_event_ack on error response", "[json][parse]") {
    auto const result = detail::parse_event_ack(
        R"({"status": "error", "message": "non-monotonic timestamp", "code": "monotonicity_violation"})");
    CHECK_FALSE(result.has_value());
    CHECK(result.error().kind() == ErrorKind::Protocol);
    CHECK_THAT(std::string{result.error().message()}, ContainsSubstring("non-monotonic timestamp"));
}

TEST_CASE("parse_validation response", "[json][parse]") {
    auto const result = detail::parse_validation(R"({
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
    auto const result = detail::parse_extraction(R"({
        "status": "success",
        "values": [
            {"name": "Speed", "value": {"numerator": 241, "denominator": 2}},
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
    CHECK(result->errors[0].name == SignalName{"BadSig"});
    CHECK(result->errors[0].reason == "overflow");
    CHECK(result->absent.size() == 1);
    CHECK(result->absent[0] == SignalName{"MuxedTemp"});
}

TEST_CASE("parse_extraction with rational values", "[json][parse]") {
    auto const result = detail::parse_extraction(R"({
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

// ── Mutation-kill cases for the binding's rational JSON parsing ─────────────
// The kernel is proven and the wire parsing here is only tested, so the
// mutation sweep is what holds these two parsers, parse_rational_dict and
// parse_rational_as_int, and each case below names the mutant it kills.

TEST_CASE("parse_extraction rejects a negative-denominator rational", "[json][parse][error]") {
    // {1,-3} must be REJECTED, not silently sign-normalized: the kernel emits a
    // positive denominator (ℕ⁺ invariant), so a negative one is a wire-format
    // violation.  Mirrors Python / Go / Rust, which all reject den <= 0 at the
    // wire rather than rewriting it.
    auto const result = detail::parse_extraction(R"({
        "status": "success",
        "values": [{"name": "Ratio", "value": {"numerator": 1, "denominator": -3}}],
        "errors": [],
        "absent": []
    })");
    CHECK_FALSE(result.has_value());
}

// ── Strict-integer wire decoder: reject floats in integer-only positions ─────
// The FFI wire and DBC integer-position fields carry exact integers or
// {numerator, denominator} rationals only.  nlohmann silently static_casts a
// JSON float to an integer type on get<intT>() (5.9 -> 5) *before* any range
// check runs, so an unguarded read would corrupt the value rather than reject
// it.  These tests pin the reject-float behavior across the three regions
// (parse_signal_value, parse_rational_dict, the integer-position helpers).
// Go, Rust, and Python already reject floats here.

TEST_CASE("parse_extraction rejects a float signal value", "[json][parse][validation]") {
    // Region 1, parse_signal_value: a bare float is a wire-format violation,
    // not a value to approximate. Exact rationals travel as a numerator and a
    // denominator; decimals are parsed by the kernel's own decimal source of
    // truth.
    auto const result = detail::parse_extraction(R"({
        "status": "success",
        "values": [{"name": "Speed", "value": 120.5}],
        "errors": [],
        "absent": []
    })");
    CHECK_FALSE(result.has_value());
}

TEST_CASE("parse_extraction still accepts integer and rational signal values",
          "[json][parse][validation]") {
    // Positive case: the canonical integer and {num,den} shapes decode after
    // the float branch is dropped.
    auto const result = detail::parse_extraction(R"({
        "status": "success",
        "values": [
            {"name": "RPM", "value": 3000},
            {"name": "Ratio", "value": {"numerator": 1, "denominator": 3}}
        ],
        "errors": [],
        "absent": []
    })");
    REQUIRE(result.has_value());
    REQUIRE(result->values.size() == 2);
    CHECK(result->values[0].value == PhysicalValue{Rational{3000, 1}});
    CHECK(result->values[1].value == PhysicalValue{Rational{1, 3}});
}

TEST_CASE("parse_extraction rejects a float rational component", "[json][parse][validation]") {
    // Region 2: parse_rational_dict guards numerator/denominator.  Without the
    // guard {"numerator": 1.5, ...} truncates to 1, fabricating the value 1/2.
    auto const result = detail::parse_extraction(R"({
        "status": "success",
        "values": [{"name": "Ratio", "value": {"numerator": 1.5, "denominator": 2}}],
        "errors": [],
        "absent": []
    })");
    CHECK_FALSE(result.has_value());
}

TEST_CASE("parse_dbc_response rejects a float in a signed integer position",
          "[json][parse][validation]") {
    // valueDescriptions[].value is a signed integer position (require_int): a
    // float must be rejected rather than truncated.
    auto const result = detail::parse_dbc_response(R"({
        "status": "success",
        "dbc": {"version": "", "messages": [{
            "id": 256, "name": "M", "dlc": 8, "sender": "", "extended": false,
            "signals": [{
                "name": "S", "startBit": 0, "length": 8, "byteOrder": "little_endian",
                "signed": false, "factor": 1, "offset": 0, "minimum": 0, "maximum": 255,
                "unit": "", "presence": "always",
                "valueDescriptions": [{"value": 1.5, "description": "x"}]
            }]
        }]}
    })");
    CHECK_FALSE(result.has_value());
}

TEST_CASE("parse_dbc_response rejects a float startBit instead of truncating",
          "[json][parse][validation]") {
    // startBit 5.5 truncates to 5, which is inside the 0-511 range — so the bug
    // would silently accept the signal with the WRONG start bit.  Pin the
    // boundary: the float is rejected, and integer 5 at the same position still
    // decodes to start_bit == 5.  (Removing the require_uint guard flips the
    // first CHECK_FALSE green->red.)
    auto const make = [](std::string const& start_bit) {
        return std::string{R"({"status":"success","dbc":{"version":"","messages":[{)"} +
               R"("id":256,"name":"M","dlc":8,"sender":"","extended":false,"signals":[{)" +
               R"("name":"S","startBit":)" + start_bit +
               R"(,"length":8,"byteOrder":"little_endian","signed":false,)" +
               R"("factor":1,"offset":0,"minimum":0,"maximum":255,"unit":"","presence":"always"}]}]}})";
    };
    CHECK_FALSE(detail::parse_dbc_response(make("5.5")).has_value());
    auto const ok = detail::parse_dbc_response(make("5"));
    REQUIRE(ok.has_value());
    REQUIRE(ok->messages.size() == 1);
    REQUIRE(ok->messages[0].signals.size() == 1);
    CHECK(ok->messages[0].signals[0].start_bit.get() == 5);
}

TEST_CASE("parse_dbc_response rejects a float in unsigned id and dlc positions",
          "[json][parse][validation]") {
    // CAN id and dlc are unsigned positions (require_uint).  A float in either
    // truncates to an in-range integer without the guard.
    auto const make = [](std::string const& id, std::string const& dlc) {
        return std::string{R"({"status":"success","dbc":{"version":"","messages":[{)"} +
               R"("id":)" + id + R"(,"name":"M","dlc":)" + dlc +
               R"(,"sender":"","extended":false,"signals":[]}]}})";
    };
    CHECK_FALSE(detail::parse_dbc_response(make("256.5", "8")).has_value());
    CHECK_FALSE(detail::parse_dbc_response(make("256", "8.5")).has_value());
}

TEST_CASE("parse_frame_data rejects a float data byte", "[json][parse][validation]") {
    // Frame data bytes are an unsigned position (require_uint): a float byte
    // must be rejected, not truncated.
    auto const bad = detail::parse_frame_data(R"({"status": "success", "data": [1, 2.5, 3]})");
    CHECK_FALSE(bad.has_value());
    auto const ok = detail::parse_frame_data(R"({"status": "success", "data": [1, 2, 3]})");
    REQUIRE(ok.has_value());
    CHECK(ok->size() == 3);
}

TEST_CASE("parse_frame_response integer property_index uses exact division",
          "[json][parse][mutation]") {
    // property_index {6,3} -> 2 (an integer field divides). Kills the
    // division-to-multiplication mutant on the return in parse_rational_as_int,
    // whose product would be 18.
    auto const result = detail::parse_frame_response(R"({
        "type": "property_batch",
        "results": [{"type": "property", "status": "fails",
                     "property_index": {"numerator": 6, "denominator": 3},
                     "timestamp": {"numerator": 3000000, "denominator": 1}}]
    })");
    REQUIRE(result.has_value());
    auto const& b = std::get<PropertyBatch>(*result);
    auto const* v = b.first_violation();
    REQUIRE(v != nullptr);
    CHECK(v->property_index == PropertyIndex{2});
}

TEST_CASE("parse_frame_response accepts a zero timestamp", "[json][parse][mutation]") {
    // A timestamp of zero is the legal lower boundary. Kills the
    // less-than-to-less-or-equal mutant on the negative-timestamp refusal in
    // the property-result parser, which would reject zero.
    auto const result = detail::parse_frame_response(R"({
        "type": "property_batch",
        "results": [{"type": "property", "status": "fails",
                     "property_index": {"numerator": 1, "denominator": 1},
                     "timestamp": {"numerator": 0, "denominator": 1}}]
    })");
    REQUIRE(result.has_value());
    auto const& b = std::get<PropertyBatch>(*result);
    auto const* v = b.first_violation();
    REQUIRE(v != nullptr);
    REQUIRE(v->timestamp.has_value());
    CHECK(*v->timestamp == Timestamp{0});
}

TEST_CASE("parse_frame_data response", "[json][parse]") {
    auto const result = detail::parse_frame_data(R"({
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
    auto const result = detail::parse_frame_response(R"({"status": "ack"})");
    REQUIRE(result.has_value());
    CHECK(std::holds_alternative<Ack>(*result));
}

TEST_CASE("parse_frame_response reads an ack whatever its spacing", "[json][parse]") {
    // The two byte-exact spellings are answered before the document is
    // parsed; any other spacing is parsed and answered by its status.
    auto const spelling =
        GENERATE(std::string_view{R"({"status":"ack"})"}, std::string_view{R"({"status": "ack"})"},
                 std::string_view{R"({ "status" : "ack" })"},
                 std::string_view{"{\n  \"status\": \"ack\"\n}"});
    auto const result = detail::parse_frame_response(spelling);
    REQUIRE(result.has_value());
    CHECK(std::holds_alternative<Ack>(*result));
}

TEST_CASE("parse_frame_response violation", "[json][parse]") {
    auto const result = detail::parse_frame_response(R"({
        "type": "property_batch",
        "results": [{
            "type": "property",
            "status": "fails",
            "property_index": 0,
            "timestamp": 5000000,
            "reason": "Speed exceeded limit"
        }]
    })");
    REQUIRE(result.has_value());
    REQUIRE(std::holds_alternative<PropertyBatch>(*result));
    auto const& b = std::get<PropertyBatch>(*result);
    auto const* v = b.first_violation();
    REQUIRE(v != nullptr);
    CHECK(v->property_index == PropertyIndex{0});
    REQUIRE(v->timestamp.has_value());
    CHECK(*v->timestamp == Timestamp{5'000'000});
    CHECK(v->reason == "Speed exceeded limit");
}

TEST_CASE("parse_frame_response violation with rational index", "[json][parse]") {
    auto const result = detail::parse_frame_response(R"({
        "type": "property_batch",
        "results": [{
            "type": "property",
            "status": "fails",
            "property_index": {"numerator": 2, "denominator": 1},
            "timestamp": {"numerator": 3000000, "denominator": 1}
        }]
    })");
    REQUIRE(result.has_value());
    auto const& b = std::get<PropertyBatch>(*result);
    auto const* v = b.first_violation();
    REQUIRE(v != nullptr);
    CHECK(v->property_index == PropertyIndex{2});
    REQUIRE(v->timestamp.has_value());
    CHECK(*v->timestamp == Timestamp{3'000'000});
}

TEST_CASE("parse_stream_result complete", "[json][parse]") {
    auto const result = detail::parse_stream_result(R"({
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
    auto const result = detail::parse_dbc_response(R"({
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
                    "unit": "",
                    "presence": "always"
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

TEST_CASE("parse_dbc_response reads a signed signal as signed", "[json][parse]") {
    auto const result = detail::parse_dbc_response(R"({
        "status": "success",
        "dbc": {
            "version": "",
            "messages": [{
                "id": 256, "name": "TestMsg", "dlc": 8, "sender": "Node1", "extended": false,
                "signals": [{
                    "name": "Torque", "startBit": 0, "length": 16,
                    "byteOrder": "little_endian", "signed": true,
                    "factor": 1, "offset": 0, "minimum": -32768, "maximum": 32767,
                    "unit": "Nm", "presence": "always"
                }]
            }]
        }
    })");
    REQUIRE(result.has_value());
    CHECK(result->messages[0].signals[0].is_signed);
}
