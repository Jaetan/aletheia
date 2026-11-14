// SPDX-FileCopyrightText: 2025 Nicolas Pelletier
// SPDX-License-Identifier: BSD-2-Clause
// Unit tests: JSON serialize/parse.
//
// Covers detail::serialize_* and detail::parse_* for commands, responses,
// DBC trees, frame payloads, and LTL formulas, and the readers of a reply's
// places.
#include "test_helpers.hpp"

#include <catch2/catch_test_macros.hpp>
#include <catch2/generators/catch_generators.hpp>
#include <catch2/matchers/catch_matchers.hpp>
#include <catch2/matchers/catch_matchers_string.hpp>

#include "detail/json.hpp"
#include "detail/reply_shape.hpp"
#include "detail/wide_json.hpp"
#include "required.hpp"
#include <aletheia/aletheia.hpp>

#include <nlohmann/json.hpp>

#include <array>
#include <concepts>
#include <cstddef>
#include <cstdint>
#include <limits>
#include <span>
#include <string>
#include <string_view>
#include <utility>
#include <variant>
#include <vector>

using aletheia::test::required;

using namespace aletheia;
using Json = nlohmann::json;
using aletheia::test::make_test_dbc;
using Catch::Matchers::ContainsSubstring;

// The reply the kernel writes for make_test_dbc(), every key it writes
// present, with `edit` applied to it.
template<typename Edit>
static auto test_dbc_reply(Edit edit) -> std::string {
    auto reply = Json::parse(aletheia::test::parsed_dbc_response_for(make_test_dbc()));
    edit(reply);
    return reply.dump();
}

// The signal of test_dbc_reply's one message.
static auto only_signal(Json& reply) -> Json& {
    return reply["dbc"]["messages"][0]["signals"][0];
}

// ===========================================================================
// Reply places
// ===========================================================================

// Declared first in the suite's first file, so it runs before any reader reads
// a reply: a lookup that answered a value for a key an object lacks would read
// past the object before any check could report it, and on a value that is not
// an object it throws, which the first check reports.
TEST_CASE("value_at answers the value a key holds and none for a key absent",
          "[json][reply_shape]") {
    CHECK(detail::value_at(detail::Json{}, "key") == nullptr);
    CHECK(detail::value_at(detail::Json("text"), "key") == nullptr);
    auto const obj = detail::parse_json(R"({"key": 1})");
    CHECK(detail::value_at(obj, "key") == &obj.at("key"));
    CHECK(detail::value_at(obj, "other") == nullptr);
}

// A natural place read into `T` reads `T`'s maximum and refuses the next.
template<std::unsigned_integral T>
static void reads_up_to_its_maximum() {
    constexpr auto max = std::numeric_limits<T>::max();
    auto const place = detail::ReplyPath{}.at("n");
    CHECK(detail::read_unsigned<T>(detail::json_of(false, max), place) == max);
    CHECK_THROWS_WITH(detail::read_unsigned<T>(
                          detail::json_of(false, static_cast<unsigned __int128>(max) + 1), place),
                      "reply n: expected number, got number");
}

TEST_CASE("a natural place reads up to its type's maximum and refuses past it",
          "[json][reply_shape]") {
    reads_up_to_its_maximum<std::uint8_t>();
    reads_up_to_its_maximum<std::uint16_t>();
    reads_up_to_its_maximum<std::uint32_t>();
    reads_up_to_its_maximum<std::uint64_t>();
}

TEST_CASE("an int64 place reads both ends of its range and refuses past either",
          "[json][reply_shape]") {
    constexpr auto high = std::numeric_limits<std::int64_t>::max();
    constexpr auto low = std::numeric_limits<std::int64_t>::min();
    constexpr auto low_magnitude = static_cast<unsigned __int128>(1) << 63U;
    auto const place = detail::ReplyPath{}.at("n");
    CHECK(detail::read_int64(detail::json_of(false, static_cast<unsigned __int128>(high)), place) ==
          high);
    CHECK(detail::read_int64(detail::json_of(true, low_magnitude), place) == low);
    CHECK_THROWS_WITH(detail::read_int64(detail::json_of(false, low_magnitude), place),
                      "reply n: expected number, got number");
    CHECK_THROWS_WITH(detail::read_int64(detail::json_of(true, low_magnitude + 1), place),
                      "reply n: expected number, got number");
}

TEST_CASE("a word place's words are quoted and joined, the last by \"or\"", "[json][reply_shape]") {
    constexpr auto spelled = std::to_array<std::string_view>({"a", "b", "c"});
    CHECK(detail::words(std::span{spelled}.first(1)) == R"("a")");
    CHECK(detail::words(std::span{spelled}.first(2)) == R"("a" or "b")");
    CHECK(detail::words(spelled) == R"("a", "b" or "c")");
}

// The refusal of the status of `reply`, which holds no word parse_success
// reads.
static auto status_refusal(std::string_view reply) -> std::string {
    auto const parsed = detail::parse_success(reply);
    REQUIRE_FALSE(parsed.has_value());
    return std::string{parsed.error().message()};
}

TEST_CASE("a word place holding no word names what came", "[json][reply_shape]") {
    // A number below -2^127, held as a binary node, is a number too.
    std::string const expected = R"(reply status: expected "success" or "error", got )";
    CHECK(status_refusal(R"({"status": 42})") == expected + "number");
    CHECK(status_refusal(R"({"status": -170141183460469231731687303715884105729})") ==
          expected + "number");
    CHECK(status_refusal(R"({"status": ["success"]})") == expected + "array");
    CHECK(status_refusal("{}") == expected + "nothing");
}

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
    // "extended" is written on every identifier, as the kernel's formatter
    // writes it.
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
    // Always-present signals carry the explicit "presence": "always".
    CHECK(sig["presence"] == "always");
}

TEST_CASE("serialize_set_properties produces correct JSON", "[json][serialize]") {
    auto formula = ltl::always(ltl::atomic(
        required(ltl::less_than(SignalName{"Speed"}, PhysicalValue{Rational{220, 1}}))));
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
    auto inner =
        ltl::atomic(required(ltl::equals(SignalName{"Brake"}, PhysicalValue{Rational{1, 1}})));
    auto formula = required(ltl::always_within(TimeBound{2'000'000}, std::move(inner)));
    std::vector<LtlFormula> props;
    props.push_back(std::move(formula));
    auto const str = required(detail::serialize_set_properties(props));
    auto j = Json::parse(str);

    CHECK(j["properties"][0]["operator"] == "metricAlways");
    CHECK(j["properties"][0]["timebound"] == 2'000'000);
}

TEST_CASE("serialize all predicate types", "[json][serialize]") {
    auto const check = [](Result<Predicate> p, std::string const& expected) {
        auto formula = ltl::atomic(required(std::move(p)));
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
    CHECK(result.error().message() == R"(reply status: expected "success" or "error", got "ack")");
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
    CHECK(result.error().message() == R"(reply status: expected "ack" or "error", got "success")");
}

TEST_CASE("parse_event_ack on error response", "[json][parse]") {
    auto const result = detail::parse_event_ack(
        R"({"status": "error", "message": "non-monotonic timestamp", "code": "handler_non_monotonic_timestamp"})");
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

// ── A number with a fraction where the kernel writes a whole number ──────────
// The kernel writes a whole number as digits and a fraction as a
// {numerator, denominator} object, never a number with a fraction or an
// exponent, so a reader refuses one wherever it comes rather than truncating
// it to a whole number the reply never stated. The refusal names the place,
// in the one form of detail/reply_shape.hpp.

TEST_CASE("parse_extraction rejects a float signal value", "[json][parse][validation]") {
    // A bare float is not a value to approximate: exact rationals travel as a
    // numerator and a denominator.
    auto const result = detail::parse_extraction(R"({
        "status": "success",
        "values": [{"name": "Speed", "value": 120.5}],
        "errors": [],
        "absent": []
    })");
    REQUIRE_FALSE(result.has_value());
    CHECK(result.error().kind() == ErrorKind::Protocol);
    CHECK(result.error().message() == "reply values/value: expected a rational, got number");
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
    // {"numerator": 1.5, ...} truncated to 1 would fabricate the value 1/2.
    auto const result = detail::parse_extraction(R"({
        "status": "success",
        "values": [{"name": "Ratio", "value": {"numerator": 1.5, "denominator": 2}}],
        "errors": [],
        "absent": []
    })");
    REQUIRE_FALSE(result.has_value());
    CHECK(result.error().message() == "reply values/value: expected a rational, got object");
}

TEST_CASE("parse_dbc_response rejects a float in a signed integer position",
          "[json][parse][validation]") {
    // valueDescriptions[].value is a signed whole number: a float is refused
    // rather than truncated.
    auto const result = detail::parse_dbc_response(test_dbc_reply([](Json& reply) {
        only_signal(reply)["valueDescriptions"] =
            Json::parse(R"([{"value": 1.5, "description": "x"}])");
    }));
    REQUIRE_FALSE(result.has_value());
    CHECK(result.error().message() ==
          "reply dbc/messages/signals/valueDescriptions/value: expected number, got number");
}

TEST_CASE("parse_dbc_response rejects a float startBit instead of truncating",
          "[json][parse][validation]") {
    // startBit 5.5 truncated to 5 would read a signal at a start bit the reply
    // never stated. Pin the boundary: the float is refused, and integer 5 at
    // the same place still decodes to start_bit == 5.
    auto const make = [](Json const& start_bit) {
        return test_dbc_reply([&](Json& reply) { only_signal(reply)["startBit"] = start_bit; });
    };
    auto const bad = detail::parse_dbc_response(make(5.5));
    REQUIRE_FALSE(bad.has_value());
    CHECK(bad.error().message() ==
          "reply dbc/messages/signals/startBit: expected number, got number");
    auto const ok = detail::parse_dbc_response(make(5));
    REQUIRE(ok.has_value());
    REQUIRE(ok->messages.size() == 1);
    REQUIRE(ok->messages[0].signals.size() == 1);
    CHECK(ok->messages[0].signals[0].start_bit.get() == 5);
}

TEST_CASE("parse_dbc_response rejects a float in unsigned id and dlc positions",
          "[json][parse][validation]") {
    // CAN id and dlc are natural places. A float in either, truncated, would
    // be a number the reply never stated.
    auto const make = [](Json const& id, Json const& dlc) {
        return test_dbc_reply([&](Json& reply) {
            reply["dbc"]["messages"][0]["id"] = id;
            reply["dbc"]["messages"][0]["dlc"] = dlc;
        });
    };
    auto const bad_id = detail::parse_dbc_response(make(256.5, 8));
    REQUIRE_FALSE(bad_id.has_value());
    CHECK(bad_id.error().message() == "reply dbc/messages/id: expected number, got number");
    auto const bad_dlc = detail::parse_dbc_response(make(256, 8.5));
    REQUIRE_FALSE(bad_dlc.has_value());
    CHECK(bad_dlc.error().message() == "reply dbc/messages/dlc: expected number, got number");
}

TEST_CASE("parse_frame_data rejects a float data byte", "[json][parse][validation]") {
    // Frame data bytes are natural places: a float byte is refused, not
    // truncated.
    auto const bad = detail::parse_frame_data(R"({"status": "success", "data": [1, 2.5, 3]})");
    REQUIRE_FALSE(bad.has_value());
    CHECK(bad.error().message() == "reply data: expected number, got number");
    auto const ok = detail::parse_frame_data(R"({"status": "success", "data": [1, 2, 3]})");
    REQUIRE(ok.has_value());
    CHECK(ok->size() == 3);
}

TEST_CASE("parse_frame_response accepts a zero timestamp", "[json][parse]") {
    // A timestamp of zero, a trace's first instant, is read as itself.
    auto const result = detail::parse_frame_response(R"({
        "type": "property_batch",
        "results": [{"type": "property", "status": "fails", "property_index": 1,
                     "timestamp": 0, "reason": "Speed exceeded limit"}]
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

TEST_CASE("parse_stream_result complete", "[json][parse]") {
    auto const result = detail::parse_stream_result(R"({
        "status": "complete",
        "results": [
            {"type": "property", "status": "holds", "property_index": 0},
            {"type": "property", "status": "fails", "property_index": 1,
             "timestamp": 5000000, "reason": "Never satisfied"},
            {"type": "property", "status": "unresolved", "property_index": 2,
             "reason": "Atomic: predicate never resolved at end of stream"}
        ],
        "warnings": []
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

TEST_CASE("an unresolved verdict carries the timestamp its key holds, a null key none",
          "[json][parse]") {
    auto const result = detail::parse_stream_result(R"({
        "status": "complete",
        "results": [
            {"type": "property", "status": "unresolved", "property_index": 0, "timestamp": 1000,
             "reason": "r"},
            {"type": "property", "status": "unresolved", "property_index": 1, "timestamp": null,
             "reason": "r"},
            {"type": "property", "status": "unresolved", "property_index": 2, "reason": "r"}
        ],
        "warnings": []
    })");
    REQUIRE(result.has_value());
    REQUIRE(result->results.size() == 3);
    CHECK(result->results[0].timestamp == Timestamp{1000});
    CHECK_FALSE(result->results[1].timestamp.has_value());
    CHECK_FALSE(result->results[2].timestamp.has_value());
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
                "senders": [],
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
                    "receivers": [],
                    "valueDescriptions": [],
                    "presence": "always"
                }]
            }],
            "signalGroups": [], "environmentVars": [], "valueTables": [], "nodes": [],
            "comments": [], "attributes": [], "unresolvedValueDescs": []
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
    auto const result = detail::parse_dbc_response(test_dbc_reply([](Json& reply) {
        auto& sig = only_signal(reply);
        sig["signed"] = true;
        sig["minimum"] = -32768;
        sig["maximum"] = 32767;
    }));
    REQUIRE(result.has_value());
    CHECK(result->messages[0].signals[0].is_signed);
    CHECK(result->messages[0].signals[0].minimum == RationalBound{Rational{-32768, 1}});
}
