// SPDX-FileCopyrightText: 2025 Nicolas Pelletier
// SPDX-License-Identifier: BSD-2-Clause
// Unit tests: one refusal per guard the JSON parser writes, each asserting
// the guard's own wording.
#include <catch2/catch_test_macros.hpp>
#include <catch2/matchers/catch_matchers.hpp>
#include <catch2/matchers/catch_matchers_string.hpp>

#include "detail/json.hpp"
#include <aletheia/aletheia.hpp>

#include <array>
#include <string>
#include <string_view>
#include <variant>

using namespace aletheia;
using Catch::Matchers::ContainsSubstring;

// ---------------------------------------------------------------------------
// One refusal per guard the parser writes. Each test feeds the one field the
// guard reads malformed and asserts the guard's own wording, so a guard that
// stops firing, and lets the field reach the accessor behind it, is told
// from one that fires: the accessor's own exception carries other words.
// ---------------------------------------------------------------------------

// A success DBC response with one message and one signal, the signal's own
// fields replaced by `signal_fields` and the DBC's top-level extras appended.
static auto dbc_response(std::string_view signal_fields, std::string_view dbc_extra = "")
    -> std::string {
    return std::string{R"({"status": "success", "dbc": {"version": "", "messages": [{
        "id": 256, "name": "M", "dlc": 8, "sender": "", "extended": false,
        "signals": [{)"} +
           std::string{signal_fields} + "}]}]" + std::string{dbc_extra} + "}}";
}

constexpr std::string_view k_plain_signal =
    R"("name": "S", "startBit": 0, "length": 8, "byteOrder": "little_endian",
        "signed": false, "factor": 1, "offset": 0, "minimum": 0, "maximum": 255,
        "unit": "", "presence": "always")";

static auto dbc_error_message(std::string_view response) -> std::string {
    auto const result = detail::parse_dbc_response(response);
    REQUIRE_FALSE(result.has_value());
    return std::string{result.error().message()};
}

TEST_CASE("parse_dbc_response refuses a string where an integer is required, by name",
          "[json][parse][refusal]") {
    auto const message = dbc_error_message(dbc_response(
        R"("name": "S", "startBit": 0, "length": 8, "byteOrder": "little_endian",
        "signed": false, "factor": {"numerator": "1", "denominator": 1}, "offset": 0,
        "minimum": 0, "maximum": 255, "unit": "", "presence": "always")"));
    CHECK_THAT(message, ContainsSubstring("must be an integer"));
}

TEST_CASE("parse_dbc_response refuses a string varType, by name", "[json][parse][refusal]") {
    auto const message = dbc_error_message(dbc_response(
        k_plain_signal,
        R"(, "environmentVars": [{"name": "E", "varType": "0", "minimum": 0, "maximum": 1,
            "unit": "", "initial": 0, "id": 0, "accessType": "", "accessNodes": []}])"));
    CHECK_THAT(message, ContainsSubstring("must be an integer"));
}

TEST_CASE("an error response lifts no issues where the issues field is missing or malformed",
          "[json][parse][refusal]") {
    // The lift degrades to no issues rather than reaching for a field that is
    // not there; a guard that stopped firing would throw from the accessor and
    // turn the validation error into a protocol one.
    for (auto const* body : {R"({"status": "error", "code": "handler_validation_failed",
                                 "message": "m", "has_errors": true})",
                             R"({"status": "error", "code": "handler_validation_failed",
                                 "message": "m", "issues": []})",
                             R"({"status": "error", "code": "handler_validation_failed",
                                 "message": "m", "has_errors": true, "issues": 5})"}) {
        auto const result = detail::parse_success(body);
        REQUIRE_FALSE(result.has_value());
        CHECK(result.error().kind() == ErrorKind::Protocol);
        CHECK(result.error().message() == "m");
        CHECK_FALSE(result.error().issues().has_value());
    }
}

TEST_CASE("a bound-exceeded error carries no bound info where a bound field is missing or "
          "malformed",
          "[json][parse][refusal]") {
    for (auto const* body : {R"({"status": "error", "code": "input_bound_exceeded", "message": "m",
              "bound_kind": 5, "observed": 1, "limit": 1})",
                             R"({"status": "error", "code": "input_bound_exceeded", "message": "m",
              "bound_kind": "k", "limit": 1})",
                             R"({"status": "error", "code": "input_bound_exceeded", "message": "m",
              "bound_kind": "k", "observed": -1, "limit": 1})",
                             R"({"status": "error", "code": "input_bound_exceeded", "message": "m",
              "bound_kind": "k", "observed": 1})",
                             R"({"status": "error", "code": "input_bound_exceeded", "message": "m",
              "bound_kind": "k", "observed": 1, "limit": "x"})",
                             R"({"status": "error", "code": "input_bound_exceeded", "message": "m",
              "field": 5, "bound_kind": "k", "observed": 1, "limit": 1})"}) {
        auto const result = detail::parse_success(body);
        REQUIRE_FALSE(result.has_value());
        CHECK(result.error().kind() == ErrorKind::InputBoundExceeded);
        CHECK(result.error().message() == "m");
        CHECK_FALSE(result.error().bound_info().has_value());
    }
}

TEST_CASE("parse_dbc_response refuses a rational that is neither an integer nor a pair, by name",
          "[json][parse][refusal]") {
    for (auto const* factor : {R"("1/2")", R"({"numerator": 1})", R"({"denominator": 2})"}) {
        auto const message = dbc_error_message(dbc_response(
            std::string{R"("name": "S", "startBit": 0, "length": 8, "byteOrder": "little_endian",
            "signed": false, "factor": )"} +
            factor + R"(, "offset": 0, "minimum": 0, "maximum": 255, "unit": "",
            "presence": "always")"));
        CHECK_THAT(message, ContainsSubstring("Expected integer or {numerator, denominator}"));
    }
}

TEST_CASE("parse_dbc_response refuses a multiplexed signal without its values, by name",
          "[json][parse][refusal]") {
    for (auto const* values : {"", R"(, "multiplex_values": 5)"}) {
        auto const message = dbc_error_message(dbc_response(
            std::string{R"("name": "S", "startBit": 0, "length": 8, "byteOrder": "little_endian",
            "signed": false, "factor": 1, "offset": 0, "minimum": 0, "maximum": 255,
            "unit": "", "presence": "multiplexed", "multiplexor": "Mux")"} +
            values));
        CHECK_THAT(message, ContainsSubstring("requires a non-empty \"multiplex_values\""));
    }
}

TEST_CASE("parse_dbc_response refuses an unknown byte order, by name", "[json][parse][refusal]") {
    auto const message = dbc_error_message(dbc_response(
        R"("name": "S", "startBit": 0, "length": 8, "byteOrder": "middle_endian",
        "signed": false, "factor": 1, "offset": 0, "minimum": 0, "maximum": 255,
        "unit": "", "presence": "always")"));
    CHECK_THAT(message, ContainsSubstring("Unrecognized byteOrder"));
}

TEST_CASE("parse_dbc_response reads an unsigned signal as unsigned, stated or defaulted",
          "[json][parse]") {
    for (auto const* fields :
         {k_plain_signal.data(),
          R"("name": "S", "startBit": 0, "length": 8, "byteOrder": "little_endian",
            "factor": 1, "offset": 0, "minimum": 0, "maximum": 255, "unit": "",
            "presence": "always")"}) {
        auto const result = detail::parse_dbc_response(dbc_response(fields));
        REQUIRE(result.has_value());
        CHECK_FALSE(result->messages.at(0).signals.at(0).is_signed);
    }
}

TEST_CASE("parse_dbc_response refuses a CAN id past its frame's range, by name",
          "[json][parse][refusal]") {
    auto const extended = detail::parse_dbc_response(R"({"status": "success", "dbc": {
        "version": "", "messages": [{"id": 536870912, "name": "M", "dlc": 8, "sender": "",
        "extended": true, "signals": []}]}})");
    REQUIRE_FALSE(extended.has_value());
    CHECK_THAT(std::string{extended.error().message()},
               ContainsSubstring("Invalid extended CAN ID"));
    auto const standard = detail::parse_dbc_response(R"({"status": "success", "dbc": {
        "version": "", "messages": [{"id": 2048, "name": "M", "dlc": 8, "sender": "",
        "extended": false, "signals": []}]}})");
    REQUIRE_FALSE(standard.has_value());
    CHECK_THAT(std::string{standard.error().message()},
               ContainsSubstring("Invalid standard CAN ID"));
}

TEST_CASE("parse_dbc_response refuses an unknown attribute scope, type, value, target and kind, "
          "by name",
          "[json][parse][refusal]") {
    struct Row {
        std::string_view attribute;
        std::string_view wording;
    };
    constexpr std::array rows = {
        Row{.attribute = R"({"kind": "definition", "name": "A", "scope": "planet",
                "attrType": {"kind": "int", "min": 0, "max": 1}})",
            .wording = "Unknown attribute scope"},
        Row{.attribute = R"({"kind": "definition", "name": "A", "scope": "node",
                "attrType": {"kind": "bogus", "min": 0, "max": 1}})",
            .wording = "Unknown attribute type kind"},
        Row{.attribute =
                R"({"kind": "default", "name": "A", "value": {"kind": "bogus", "value": 1}})",
            .wording = "Unknown attribute value kind"},
        Row{.attribute = R"({"kind": "assignment", "name": "A", "target": {"kind": "bogus"},
                "value": {"kind": "int", "value": 1}})",
            .wording = "Unknown attribute target kind"},
        Row{.attribute = R"({"kind": "bogus", "name": "A"})", .wording = "Unknown attribute kind"},
    };
    for (auto const& row : rows) {
        auto const message = dbc_error_message(dbc_response(
            k_plain_signal, std::string{", \"attributes\": ["} + std::string{row.attribute} + "]"));
        CHECK_THAT(message, ContainsSubstring(std::string{row.wording}));
    }
}

TEST_CASE("parse_frame_response reads a non-string reason as none", "[json][parse][refusal]") {
    auto const result = detail::parse_frame_response(
        R"({"status": "success", "type": "property_batch",
            "results": [{"status": "fails", "property_index": 0, "reason": 5}]})");
    REQUIRE(result.has_value());
    auto const* batch = std::get_if<PropertyBatch>(&*result);
    REQUIRE(batch != nullptr);
    CHECK(batch->results.at(0).reason.empty());
}

TEST_CASE("parse_frame_response refuses a results field that is not an array, by name",
          "[json][parse][refusal]") {
    auto const result = detail::parse_frame_response(
        R"({"status": "success", "type": "property_batch", "results": 5})");
    REQUIRE_FALSE(result.has_value());
    CHECK_THAT(std::string{result.error().message()},
               ContainsSubstring("must be a non-empty array"));
}

TEST_CASE("the DBC responses refuse a missing dbc field, by name", "[json][parse][refusal]") {
    auto const parsed = detail::parse_dbc_response(R"({"status": "success"})");
    REQUIRE_FALSE(parsed.has_value());
    CHECK_THAT(std::string{parsed.error().message()}, ContainsSubstring("Missing 'dbc' field"));
    auto const text = detail::parse_parsed_dbc(R"({"status": "success"})");
    REQUIRE_FALSE(text.has_value());
    CHECK_THAT(std::string{text.error().message()}, ContainsSubstring("Missing 'dbc' field"));
}

TEST_CASE("parse_parsed_dbc reads a response without warnings as one with none",
          "[json][parse][refusal]") {
    auto const result = detail::parse_parsed_dbc(R"({"status": "success", "dbc": {
        "version": "", "messages": []}})");
    REQUIRE(result.has_value());
    CHECK(result->warnings.empty());
}

TEST_CASE("the issue lists refuse an unknown severity, by name", "[json][parse][refusal]") {
    auto const warnings = detail::parse_parsed_dbc(R"({"status": "success", "dbc": {
        "version": "", "messages": []}, "warnings": [{"severity": "bogus", "code": "c",
        "detail": ""}]})");
    REQUIRE_FALSE(warnings.has_value());
    CHECK_THAT(std::string{warnings.error().message()},
               ContainsSubstring("Unknown validation severity"));
    auto const issues = detail::parse_dbc_text_response(R"({"status": "success", "text": "",
        "issues": [{"severity": "bogus", "code": "c", "detail": ""}]})");
    REQUIRE_FALSE(issues.has_value());
    CHECK_THAT(std::string{issues.error().message()},
               ContainsSubstring("Unknown validation severity"));
}

TEST_CASE("parse_dbc_text_response refuses a non-string text, by name", "[json][parse][refusal]") {
    auto const result = detail::parse_dbc_text_response(R"({"status": "success", "text": 5})");
    REQUIRE_FALSE(result.has_value());
    CHECK_THAT(std::string{result.error().message()},
               ContainsSubstring("Missing or non-string 'text'"));
}

TEST_CASE("parse_frame_response refuses an unknown verdict status, by name",
          "[json][parse][refusal]") {
    auto const result = detail::parse_frame_response(
        R"({"status": "success", "type": "property_batch",
            "results": [{"status": "maybe", "property_index": 0}]})");
    REQUIRE_FALSE(result.has_value());
    CHECK_THAT(std::string{result.error().message()}, ContainsSubstring("Unknown verdict status"));
}
