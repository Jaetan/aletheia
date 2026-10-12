// SPDX-FileCopyrightText: 2025 Nicolas Pelletier
// SPDX-License-Identifier: BSD-2-Clause
// Unit tests: the JSON response decoders on malformed input, missing fields,
// out-of-range values and edge-case shapes such as empty arrays.
#include <catch2/catch_test_macros.hpp>
#include <catch2/matchers/catch_matchers.hpp>
#include <catch2/matchers/catch_matchers_string.hpp>

#include "detail/json.hpp"
#include <aletheia/aletheia.hpp>

#include <cstddef>
#include <ranges>
#include <string>

using namespace aletheia;
using Catch::Matchers::ContainsSubstring;

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
    for (auto const i : std::views::iota(0, 64)) {
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
    // The post-batch-shape error message reports both status= and type= since
    // the discriminator moved.
    CHECK_THAT(std::string{result.error().message()},
               ContainsSubstring("Unexpected frame response"));
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

TEST_CASE("parse_validation preserves the wire string for an unknown issue code", "[json][parse]") {
    auto result = detail::parse_validation(R"({
        "status": "validation",
        "has_errors": true,
        "issues": [
            {"severity": "error", "code": "some_future_code", "detail": "New check"}
        ]
    })");
    REQUIRE(result.has_value());
    // The enum degrades to Unknown (forward-compatible)...
    CHECK(result->issues[0].code == IssueCode::Unknown);
    // ...but the original wire code survives (round-trips) rather than being lost
    // to the literal "unknown" — matching Go / Rust / Python.
    CHECK(result->issues[0].code_raw == "some_future_code");
    CHECK(issue_code_label(result->issues[0]) == "some_future_code");
}

TEST_CASE("issue_code_label falls back to the enum's spelling when the wire code is empty",
          "[json][parse]") {
    auto result = detail::parse_validation(R"({
        "status": "validation",
        "has_errors": true,
        "issues": [{"severity": "error", "code": "", "detail": "unnamed"}]
    })");
    REQUIRE(result.has_value());
    CHECK(result->issues[0].code == IssueCode::Unknown);
    CHECK(result->issues[0].code_raw.empty());
    CHECK(issue_code_label(result->issues[0]) == to_string(IssueCode::Unknown));
}

TEST_CASE("issue_code_label renders the canonical spelling for a known code", "[json][parse]") {
    auto result = detail::parse_validation(R"({
        "status": "validation",
        "has_errors": true,
        "issues": [
            {"severity": "error", "code": "factor_zero", "detail": "factor is zero"}
        ]
    })");
    REQUIRE(result.has_value());
    CHECK(result->issues[0].code == IssueCode::FactorZero);
    CHECK(issue_code_label(result->issues[0]) == "factor_zero");
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
