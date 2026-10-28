// SPDX-FileCopyrightText: 2025 Nicolas Pelletier
// SPDX-License-Identifier: BSD-2-Clause
// Unit tests: the JSON response decoders' refusals, chiefly of malformed
// rationals, missing fields and out-of-range indices, bytes and CAN
// identifiers; and the ExtractionResult::get accessor.
#include <catch2/catch_test_macros.hpp>
#include <catch2/matchers/catch_matchers.hpp>
#include <catch2/matchers/catch_matchers_string.hpp>

#include "detail/json.hpp"
#include <aletheia/aletheia.hpp>

#include <string>

using namespace aletheia;
using Catch::Matchers::ContainsSubstring;

TEST_CASE("parse_extraction rejects zero denominator in rational", "[json][parse][error]") {
    auto const result = detail::parse_extraction(R"({
        "status": "success",
        "values": [{"name": "Bad", "value": {"numerator": 1, "denominator": 0}}],
        "errors": [], "absent": []
    })");
    CHECK_FALSE(result.has_value());
    // Assert parse_rational_dict's own "Non-positive denominator" wording, not
    // just "denominator": the latter also matches the Rational ctor's
    // "denominator must be positive", so a den == 0 check that fell through to
    // {num, 0} would pass a loose match. (den == 0 is rejected by the same
    // den <= 0 guard that rejects negative denominators.)
    CHECK_THAT(std::string{result.error().message()},
               ContainsSubstring("Non-positive denominator"));
}

TEST_CASE("parse_frame_response rejects zero denominator in timestamp", "[json][parse][error]") {
    auto const result = detail::parse_frame_response(R"({
        "type": "property_batch",
        "results": [{
            "type": "property",
            "status": "fails",
            "property_index": 0,
            "timestamp": {"numerator": 1000, "denominator": 0}
        }]
    })");
    CHECK_FALSE(result.has_value());
    CHECK_THAT(std::string{result.error().message()}, ContainsSubstring("denominator"));
}

TEST_CASE("parse_stream_result rejects malformed JSON", "[json][parse][error]") {
    auto const result = detail::parse_stream_result("not json");
    CHECK_FALSE(result.has_value());
    CHECK(result.error().kind() == ErrorKind::Protocol);
}

TEST_CASE("parse_stream_result rejects missing results field", "[json][parse][error]") {
    auto const result = detail::parse_stream_result(R"({"status": "complete"})");
    CHECK_FALSE(result.has_value());
    CHECK(result.error().kind() == ErrorKind::Protocol);
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
    CHECK_FALSE(result.has_value());
    CHECK(result.error().kind() == ErrorKind::Protocol);
    CHECK_THAT(std::string{result.error().message()}, ContainsSubstring("Negative property_index"));
}

TEST_CASE("parse_frame_response rejects a property_index above the signed 64-bit range",
          "[json][parse][error]") {
    // One past the signed maximum arrives as an unsigned number.  Narrowed
    // without a range check it wraps to the most negative value, and the sign
    // test below it then reports a negative index the document never carried.
    auto const result = detail::parse_frame_response(R"({
        "type": "property_batch",
        "results": [{
            "type": "property",
            "status": "fails",
            "property_index": 9223372036854775808,
            "timestamp": 100
        }]
    })");
    CHECK_FALSE(result.has_value());
    CHECK(result.error().kind() == ErrorKind::Protocol);
    CHECK_THAT(std::string{result.error().message()}, ContainsSubstring("out of range"));
    CHECK_THAT(std::string{result.error().message()},
               !ContainsSubstring("Negative property_index"));
}

TEST_CASE("parse_frame_data rejects a data byte above a byte", "[json][parse][validation]") {
    // 256 narrows to zero without a range check, so the payload would decode
    // one byte the document did not state.
    auto const bad = detail::parse_frame_data(R"({"status": "success", "data": [1, 256, 3]})");
    CHECK_FALSE(bad.has_value());
    CHECK_THAT(std::string{bad.error().message()}, ContainsSubstring("out of range"));
    auto const ok = detail::parse_frame_data(R"({"status": "success", "data": [1, 255, 3]})");
    REQUIRE(ok.has_value());
    CHECK(ok->size() == 3);
}

TEST_CASE("parse_dbc_response rejects a CAN id above the 32-bit position",
          "[json][parse][validation]") {
    // The id position narrows to 32 bits.  2^32 wraps to zero, which is a
    // valid standard id, so the message would decode under an id the document
    // never stated.
    auto const make = [](std::string const& id) {
        return std::string{R"({"status":"success","dbc":{"version":"","messages":[{)"} +
               R"("id":)" + id +
               R"(,"name":"M","dlc":8,"sender":"","extended":true,"signals":[]}]}})";
    };
    auto const bad = detail::parse_dbc_response(make("4294967296"));
    CHECK_FALSE(bad.has_value());
    CHECK_THAT(std::string{bad.error().message()}, ContainsSubstring("out of range"));
    auto const ok = detail::parse_dbc_response(make("536870911"));
    REQUIRE(ok.has_value());
    REQUIRE(ok->messages.size() == 1);
    CHECK(std::get<ExtendedId>(ok->messages[0].id).value() == 536870911);
}

TEST_CASE("parse_stream_result rejects negative property_index", "[json][parse][error]") {
    auto const result = detail::parse_stream_result(R"({
        "status": "complete",
        "results": [{"status": "holds", "property_index": -5}]
    })");
    CHECK_FALSE(result.has_value());
    CHECK(result.error().kind() == ErrorKind::Protocol);
    CHECK_THAT(std::string{result.error().message()}, ContainsSubstring("Negative property_index"));
}

// `timestamp` is optional at the parse layer, because an end-of-stream entry
// that holds carries none. The kernel always emits one on a streaming failure,
// and that contract is enforced upstream rather than here. The negative and
// non-integer refusals do apply.
TEST_CASE("parse_frame_response accepts fails with missing timestamp", "[json][parse]") {
    auto const result = detail::parse_frame_response(R"({
        "type": "property_batch",
        "results": [{
            "type": "property",
            "status": "fails",
            "property_index": 0
        }]
    })");
    REQUIRE(result.has_value());
    auto const& b = std::get<PropertyBatch>(*result);
    auto const* v = b.first_violation();
    REQUIRE(v != nullptr);
    CHECK_FALSE(v->timestamp.has_value());
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
    CHECK_FALSE(result.has_value());
    CHECK(result.error().kind() == ErrorKind::Protocol);
}

TEST_CASE("parse_stream_result rejects entry with missing status", "[json][parse][error]") {
    auto const result = detail::parse_stream_result(R"({
        "status": "complete",
        "results": [{"property_index": 0}]
    })");
    CHECK_FALSE(result.has_value());
    CHECK(result.error().kind() == ErrorKind::Protocol);
    CHECK_THAT(std::string{result.error().message()}, ContainsSubstring("Unknown verdict status"));
}

TEST_CASE("parse_rational_as_int rejects non-exact rational", "[json][parse][error]") {
    // {"numerator": 3, "denominator": 2} → 1.5, not an integer
    auto const result = detail::parse_frame_response(R"({
        "type": "property_batch",
        "results": [{
            "type": "property",
            "status": "fails",
            "property_index": {"numerator": 3, "denominator": 2},
            "timestamp": 100
        }]
    })");
    CHECK_FALSE(result.has_value());
    CHECK(result.error().kind() == ErrorKind::Protocol);
    CHECK_THAT(std::string{result.error().message()}, ContainsSubstring("Non-exact rational"));
}

TEST_CASE("parse_frame_response rejects unrecognised top-level type", "[json][parse][error]") {
    // Violations live inside a property batch's results, so a top-level
    // failure status is not a shape the parser knows. Any top-level shape
    // other than an acknowledgement, an error or a property batch is a
    // protocol violation.
    auto const result = detail::parse_frame_response(R"({
        "status": "fails",
        "property_index": 0,
        "timestamp": 100
    })");
    CHECK_FALSE(result.has_value());
    CHECK(result.error().kind() == ErrorKind::Protocol);
    CHECK_THAT(std::string{result.error().message()},
               ContainsSubstring("Unexpected frame response"));
}

TEST_CASE("parse_rational rejects float input", "[json][parse][error]") {
    // A floating-point 1.5 should be rejected (not integer, not {num, den} dict)
    auto const result = detail::parse_dbc_response(R"({
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
    auto const result = detail::parse_dbc_response(R"({
        "status": "success",
        "dbc": {
            "version": "", "messages": [{
                "id": 2047, "name": "Max", "dlc": 8,
                "extended": false, "signals": []
            }]
        }
    })");
    REQUIRE(result.has_value());
    auto const& id = result->messages[0].id;
    CHECK(std::get<StandardId>(id).value() == 2047);
}

TEST_CASE("parse_dbc_response rejects standard CAN ID at boundary (2048)", "[json][parse][error]") {
    auto const result = detail::parse_dbc_response(R"({
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
    auto const result = detail::parse_dbc_response(R"({
        "status": "success",
        "dbc": {
            "version": "", "messages": [{
                "id": 70000, "name": "Bad", "dlc": 8,
                "extended": false, "signals": []
            }]
        }
    })");
    CHECK_FALSE(result.has_value());
    CHECK_THAT(std::string{result.error().message()}, ContainsSubstring("exceeds 16 bits"));
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
