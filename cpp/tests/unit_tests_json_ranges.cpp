// SPDX-FileCopyrightText: 2025 Nicolas Pelletier
// SPDX-License-Identifier: BSD-2-Clause
// Unit tests: the JSON response decoders' refusals of whole-number places,
// chiefly a sign, a fraction or a width the place's own type does not hold,
// and of missing fields; and the ExtractionResult::get accessor.
#include <catch2/catch_test_macros.hpp>
#include <catch2/matchers/catch_matchers.hpp>
#include <catch2/matchers/catch_matchers_string.hpp>

#include "detail/json.hpp"
#include "test_helpers.hpp"
#include <aletheia/aletheia.hpp>

#include <nlohmann/json.hpp>

#include <cstdint>
#include <limits>
#include <string>

using namespace aletheia;
using Catch::Matchers::StartsWith;
using Json = nlohmann::json;

// The reply the kernel writes for make_test_dbc(), every key it writes
// present, with `edit` applied to its one message.
template<typename Edit>
static auto test_dbc_reply(Edit edit) -> std::string {
    auto reply = Json::parse(test::parsed_dbc_response_for(test::make_test_dbc()));
    edit(reply["dbc"]["messages"][0]);
    return reply.dump();
}

TEST_CASE("parse_frame_response rejects a timestamp written as a rational object",
          "[json][parse][error]") {
    // A timestamp is a whole number, which the kernel writes as digits.
    auto const result = detail::parse_frame_response(R"({
        "type": "property_batch",
        "results": [{
            "type": "property",
            "status": "fails",
            "property_index": 0,
            "timestamp": {"numerator": 1000, "denominator": 1},
            "reason": "r"
        }]
    })");
    REQUIRE_FALSE(result.has_value());
    CHECK(result.error().message() == "reply results/timestamp: expected number, got object");
}

TEST_CASE("parse_frame_response rejects a timestamp past the int64 range a frame is sent in",
          "[json][parse][error]") {
    // A batch's timestamp echoes a frame's, which the binding sends as an
    // int64, so a number past one is no timestamp the kernel writes back.
    auto const make = [](std::string const& timestamp) {
        return R"({"type": "property_batch", "results": [{"type": "property",
                   "status": "fails", "property_index": 0, "timestamp": )" +
               timestamp + R"(, "reason": "r"}]})";
    };
    auto const bad = detail::parse_frame_response(make("9223372036854775808"));
    REQUIRE_FALSE(bad.has_value());
    CHECK(bad.error().message() == "reply results/timestamp: expected number, got number");
    auto const ok = detail::parse_frame_response(make("9223372036854775807"));
    REQUIRE(ok.has_value());
    auto const* v = std::get<PropertyBatch>(*ok).first_violation();
    REQUIRE(v != nullptr);
    CHECK(v->timestamp == Timestamp{std::numeric_limits<Timestamp::rep>::max()});
}

TEST_CASE("parse_stream_result rejects malformed JSON", "[json][parse][error]") {
    auto const result = detail::parse_stream_result("not json");
    REQUIRE_FALSE(result.has_value());
    CHECK(result.error().kind() == ErrorKind::Protocol);
    CHECK_THAT(std::string{result.error().message()},
               StartsWith("reply: expected JSON text, got "));
}

TEST_CASE("parse_stream_result rejects missing results field", "[json][parse][error]") {
    auto const result = detail::parse_stream_result(R"({"status": "complete", "warnings": []})");
    REQUIRE_FALSE(result.has_value());
    CHECK(result.error().kind() == ErrorKind::Protocol);
    CHECK(result.error().message() == "reply results: expected array, got nothing");
}

TEST_CASE("parse_stream_result rejects missing warnings field", "[json][parse][error]") {
    auto const result = detail::parse_stream_result(R"({"status": "complete", "results": []})");
    REQUIRE_FALSE(result.has_value());
    CHECK(result.error().message() == "reply warnings: expected array, got nothing");
}

TEST_CASE("parse_frame_response rejects negative property_index", "[json][parse][error]") {
    auto const result = detail::parse_frame_response(R"({
        "type": "property_batch",
        "results": [{
            "type": "property",
            "status": "fails",
            "property_index": -1,
            "timestamp": 100
        }]
    })");
    REQUIRE_FALSE(result.has_value());
    CHECK(result.error().kind() == ErrorKind::Protocol);
    CHECK(result.error().message() == "reply results/property_index: expected number, got number");
}

TEST_CASE("parse_frame_data rejects a data byte above a byte", "[json][parse][validation]") {
    // 256 narrowed to a byte would be zero, a byte the reply did not state.
    auto const bad = detail::parse_frame_data(R"({"status": "success", "data": [1, 256, 3]})");
    REQUIRE_FALSE(bad.has_value());
    CHECK(bad.error().message() == "reply data: expected number, got number");
    auto const ok = detail::parse_frame_data(R"({"status": "success", "data": [1, 255, 3]})");
    REQUIRE(ok.has_value());
    CHECK(ok->size() == 3);
}

TEST_CASE("parse_dbc_response rejects a CAN id above the 32-bit position",
          "[json][parse][validation]") {
    // An extended id is read at 32 bits. 2^32 narrowed would be zero, so the
    // message would decode under an id the reply never stated.
    auto const make = [](std::uint64_t id) {
        return test_dbc_reply([id](Json& message) {
            message["id"] = id;
            message["extended"] = true;
        });
    };
    auto const bad = detail::parse_dbc_response(make(std::uint64_t{1} << 32U));
    REQUIRE_FALSE(bad.has_value());
    CHECK(bad.error().message() == "reply dbc/messages/id: expected number, got number");
    auto const ok = detail::parse_dbc_response(make(536870911));
    REQUIRE(ok.has_value());
    REQUIRE(ok->messages.size() == 1);
    CHECK(std::get<ExtendedId>(ok->messages[0].id).value() == 536870911);
}

TEST_CASE("parse_stream_result rejects negative property_index", "[json][parse][error]") {
    auto const result = detail::parse_stream_result(R"({
        "status": "complete",
        "results": [{"status": "holds", "property_index": -5}],
        "warnings": []
    })");
    REQUIRE_FALSE(result.has_value());
    CHECK(result.error().kind() == ErrorKind::Protocol);
    CHECK(result.error().message() == "reply results/property_index: expected number, got number");
}

// A failure carries the timestamp of the frame that broke the property and a
// reason: the kernel writes both on every failure.
TEST_CASE("parse_frame_response rejects fails with missing timestamp", "[json][parse][error]") {
    auto const result = detail::parse_frame_response(R"({
        "type": "property_batch",
        "results": [{
            "type": "property",
            "status": "fails",
            "property_index": 0,
            "reason": "r"
        }]
    })");
    REQUIRE_FALSE(result.has_value());
    CHECK(result.error().message() == "reply results/timestamp: expected number, got nothing");
}

TEST_CASE("parse_frame_response rejects fails with missing reason", "[json][parse][error]") {
    auto const result = detail::parse_frame_response(R"({
        "type": "property_batch",
        "results": [{"type": "property", "status": "fails", "property_index": 0, "timestamp": 1}]
    })");
    REQUIRE_FALSE(result.has_value());
    CHECK(result.error().message() == "reply results/reason: expected string, got nothing");
}

TEST_CASE("parse_frame_response rejects fails with missing property_index",
          "[json][parse][error]") {
    auto const result = detail::parse_frame_response(R"({
        "type": "property_batch",
        "results": [{
            "type": "property",
            "status": "fails",
            "timestamp": 100
        }]
    })");
    REQUIRE_FALSE(result.has_value());
    CHECK(result.error().kind() == ErrorKind::Protocol);
    CHECK(result.error().message() == "reply results/property_index: expected number, got nothing");
}

TEST_CASE("parse_stream_result rejects entry with missing status", "[json][parse][error]") {
    auto const result = detail::parse_stream_result(R"({
        "status": "complete",
        "results": [{"property_index": 0}],
        "warnings": []
    })");
    REQUIRE_FALSE(result.has_value());
    CHECK(result.error().kind() == ErrorKind::Protocol);
    CHECK(result.error().message() == "reply results/status: expected string, got nothing");
}

TEST_CASE("parse_frame_response rejects a property_index written as a rational object",
          "[json][parse][error]") {
    // An index is a whole number, which the kernel writes as digits.
    auto const result = detail::parse_frame_response(R"({
        "type": "property_batch",
        "results": [{
            "type": "property",
            "status": "fails",
            "property_index": {"numerator": 2, "denominator": 1},
            "timestamp": 100
        }]
    })");
    REQUIRE_FALSE(result.has_value());
    CHECK(result.error().kind() == ErrorKind::Protocol);
    CHECK(result.error().message() == "reply results/property_index: expected number, got object");
}

TEST_CASE("parse_frame_response rejects unrecognised top-level type", "[json][parse][error]") {
    // Violations live inside a property batch's results, so a top-level
    // failure status is not a shape the parser knows: a reply with a status
    // is an acknowledgement or an error.
    auto const result = detail::parse_frame_response(R"({
        "status": "fails",
        "property_index": 0,
        "timestamp": 100
    })");
    REQUIRE_FALSE(result.has_value());
    CHECK(result.error().kind() == ErrorKind::Protocol);
    CHECK(result.error().message() == R"(reply status: expected "ack" or "error", got "fails")");
}

TEST_CASE("parse_rational rejects float input", "[json][parse][error]") {
    // A floating-point 1.5 is neither digits nor a {numerator, denominator}
    // object.
    auto const result = detail::parse_dbc_response(
        test_dbc_reply([](Json& message) { message["signals"][0]["factor"] = 1.5; }));
    REQUIRE_FALSE(result.has_value());
    CHECK(result.error().kind() == ErrorKind::Protocol);
    CHECK(result.error().message() ==
          "reply dbc/messages/signals/factor: expected a rational, got number");
}

TEST_CASE("parse_dbc_response accepts standard CAN ID at boundary (2047)", "[json][parse]") {
    auto const result =
        detail::parse_dbc_response(test_dbc_reply([](Json& message) { message["id"] = 2047; }));
    REQUIRE(result.has_value());
    auto const& id = result->messages[0].id;
    CHECK(std::get<StandardId>(id).value() == 2047);
}

TEST_CASE("parse_dbc_response rejects truncating standard CAN ID (70000)", "[json][parse][error]") {
    // A standard id is read at 16 bits, and 70000 narrowed would be 4464.
    auto const result =
        detail::parse_dbc_response(test_dbc_reply([](Json& message) { message["id"] = 70000; }));
    REQUIRE_FALSE(result.has_value());
    CHECK(result.error().message() == "reply dbc/messages/id: expected number, got number");
}

TEST_CASE("ExtractionResult::get helper", "[response]") {
    ExtractionResult const result{
        .values =
            {
                {.name = SignalName{"Speed"}, .value = PhysicalValue{Rational{120, 1}}},
                {.name = SignalName{"RPM"}, .value = PhysicalValue{Rational{3000, 1}}},
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
