// SPDX-FileCopyrightText: 2025 Nicolas Pelletier
// SPDX-License-Identifier: BSD-2-Clause
// Unit tests: the JSON response decoders on malformed input, missing fields
// and edge-case shapes such as empty arrays.
#include <catch2/catch_test_macros.hpp>
#include <catch2/matchers/catch_matchers.hpp>
#include <catch2/matchers/catch_matchers_string.hpp>

#include "detail/json.hpp"
#include <aletheia/aletheia.hpp>

#include <cstddef>
#include <ranges>
#include <string>
#include <string_view>

using namespace aletheia;
using Catch::Matchers::StartsWith;

// A DBC reply with no messages, every array the kernel writes present.
static constexpr std::string_view empty_dbc_arrays =
    R"("signalGroups": [], "environmentVars": [], "valueTables": [], "nodes": [],
       "comments": [], "attributes": [], "unresolvedValueDescs": [])";

// ===========================================================================
// JSON parse error + edge-case tests
// ===========================================================================

TEST_CASE("parse_success rejects malformed JSON", "[json][parse][error]") {
    auto const result = detail::parse_success("not json at all");
    REQUIRE_FALSE(result.has_value());
    CHECK(result.error().kind() == ErrorKind::Protocol);
    CHECK_THAT(std::string{result.error().message()},
               StartsWith("reply: expected JSON text, got "));
}

TEST_CASE("parse_success rejects missing status field", "[json][parse][error]") {
    auto const result = detail::parse_success(R"({"foo": "bar"})");
    REQUIRE_FALSE(result.has_value());
    CHECK(result.error().kind() == ErrorKind::Protocol);
    CHECK(result.error().message() ==
          R"(reply status: expected "success" or "error", got nothing)");
}

TEST_CASE("parse_extraction rejects missing status field", "[json][parse][error]") {
    auto const result = detail::parse_extraction(R"({"values": []})");
    REQUIRE_FALSE(result.has_value());
    CHECK(result.error().kind() == ErrorKind::Protocol);
    CHECK(result.error().message() ==
          R"(reply status: expected "success" or "error", got nothing)");
}

TEST_CASE("parse_extraction refuses a reply lacking an array the kernel writes",
          "[json][parse][error]") {
    // The kernel writes the values, the errors and the absent signals on
    // every extraction, each array empty or not, so a reply lacking one is
    // refused at the first missing.
    auto const none = detail::parse_extraction(R"({"status": "success"})");
    REQUIRE_FALSE(none.has_value());
    CHECK(none.error().kind() == ErrorKind::Protocol);
    CHECK(none.error().message() == "reply values: expected array, got nothing");
    auto const no_absent =
        detail::parse_extraction(R"({"status": "success", "values": [], "errors": []})");
    REQUIRE_FALSE(no_absent.has_value());
    CHECK(no_absent.error().message() == "reply absent: expected array, got nothing");
}

TEST_CASE("parse_frame_data accepts variable-length data", "[json][parse]") {
    auto const result = detail::parse_frame_data(R"({"status": "success", "data": [1, 2, 3]})");
    REQUIRE(result.has_value());
    CHECK(result->size() == 3);
    CHECK((*result)[0] == std::byte{1});
    CHECK((*result)[2] == std::byte{3});
}

TEST_CASE("parse_frame_data accepts CAN-FD 64-byte data", "[json][parse]") {
    // DLC 15 → 64 bytes
    std::string json_str = R"({"status": "success", "data": [)";
    for (auto const i : std::views::iota(0, 64)) {
        if (i > 0)
            json_str += ", ";
        json_str += std::to_string(i);
    }
    json_str += "]}";
    auto const result = detail::parse_frame_data(json_str);
    REQUIRE(result.has_value());
    CHECK(result->size() == 64);
    CHECK((*result)[0] == std::byte{0});
    CHECK((*result)[63] == std::byte{63});
}

TEST_CASE("parse_frame_response rejects empty status", "[json][parse][error]") {
    auto const result = detail::parse_frame_response(R"({"foo": "bar"})");
    REQUIRE_FALSE(result.has_value());
    // A reply with no status is a batch, told by its type.
    CHECK(result.error().message() == R"(reply type: expected "property_batch", got nothing)");
}

TEST_CASE("parse_dbc_response rejects missing dbc field", "[json][parse][error]") {
    auto const result = detail::parse_dbc_response(R"({"status": "success"})");
    REQUIRE_FALSE(result.has_value());
    CHECK(result.error().message() == "reply dbc: expected object, got nothing");
}

TEST_CASE("parse_dbc_response rejects malformed signal", "[json][parse][error]") {
    auto const result = detail::parse_dbc_response(R"({
        "status": "success",
        "dbc": {
            "version": "1.0",
            "messages": [{
                "id": 256, "name": "Msg", "dlc": 8,
                "signals": [{"MISSING_NAME": true}]
            }]
        }
    })");
    REQUIRE_FALSE(result.has_value());
    CHECK(result.error().kind() == ErrorKind::Protocol);
    CHECK(result.error().message() ==
          "reply dbc/messages/signals/name: expected string, got nothing");
}

TEST_CASE("parse_dbc_response with empty messages array", "[json][parse]") {
    auto const result = detail::parse_dbc_response(
        std::string{R"({"status": "success", "dbc": {"version": "1.0", "messages": [], )"} +
        std::string{empty_dbc_arrays} + "}}");
    REQUIRE(result.has_value());
    CHECK(result->messages.empty());
    CHECK(result->version == "1.0");
}

TEST_CASE("parse_dbc_response with empty signals array", "[json][parse]") {
    auto const result = detail::parse_dbc_response(
        std::string{R"({"status": "success", "dbc": {"version": "", "messages": [{
            "id": 256, "name": "EmptyMsg", "dlc": 8, "sender": "", "senders": [],
            "extended": false, "signals": []}], )"} +
        std::string{empty_dbc_arrays} + "}}");
    REQUIRE(result.has_value());
    CHECK(result->messages.size() == 1);
    CHECK(result->messages[0].signals.empty());
}

TEST_CASE("to_string renders a decoded issue code in its wire spelling", "[json][parse]") {
    auto const result = detail::parse_validation(R"({
        "status": "validation",
        "has_errors": true,
        "issues": [
            {"severity": "error", "code": "factor_zero", "detail": "factor is zero"}
        ]
    })");
    REQUIRE(result.has_value());
    CHECK(result->issues[0].code == IssueCode::FactorZero);
    CHECK(to_string(result->issues[0].code) == "factor_zero");
}

TEST_CASE("parse_validation rejects missing severity string", "[json][parse][error]") {
    auto const result = detail::parse_validation(R"({
        "status": "validation",
        "has_errors": false,
        "issues": [
            {"code": "empty_message", "detail": "x"}
        ]
    })");
    REQUIRE_FALSE(result.has_value());
    CHECK(result.error().kind() == ErrorKind::Protocol);
    CHECK(result.error().message() ==
          R"(reply issues/severity: expected "error" or "warning", got nothing)");
}

TEST_CASE("parse_extraction rejects a string where a rational belongs", "[json][parse][error]") {
    auto const result = detail::parse_extraction(R"({
        "status": "success",
        "values": [{"name": "Bad", "value": "not_a_number"}]
    })");
    REQUIRE_FALSE(result.has_value());
    CHECK(result.error().kind() == ErrorKind::Protocol);
    CHECK(result.error().message() == "reply values/value: expected a rational, got string");
}

TEST_CASE("parse_dbc_response rejects a byte count no DLC code stands for",
          "[json][parse][error]") {
    // A message's length is written as its byte count, and 99 bytes is no
    // count a DLC code denotes.
    auto const result = detail::parse_dbc_response(R"({
        "status": "success",
        "dbc": {
            "version": "",
            "messages": [{
                "id": 256, "name": "Bad", "dlc": 99,
                "extended": false, "signals": []
            }]
        }
    })");
    REQUIRE_FALSE(result.has_value());
    CHECK(result.error().message() == "reply dbc/messages/dlc: expected number, got number");
}
