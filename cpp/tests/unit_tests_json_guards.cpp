// SPDX-FileCopyrightText: 2025 Nicolas Pelletier
// SPDX-License-Identifier: BSD-2-Clause
// Unit tests: each place of a reply refused in the one form the four bindings
// share, and each tag word outside its set read as the set's last arm.
#include <catch2/catch_test_macros.hpp>

#include "detail/json.hpp"
#include "test_helpers.hpp"
#include <aletheia/aletheia.hpp>

#include <nlohmann/json.hpp>

#include <array>
#include <string>
#include <string_view>
#include <variant>

using namespace aletheia;
using Json = nlohmann::json;

// ---------------------------------------------------------------------------
// One refusal per place a reader reads. Each test feeds the one place
// malformed and asserts the refusal's text, "reply <path>: expected <what>,
// got <what came>", so a place read by the wrong kind, or not read at all, is
// told by the path and the kinds the text names.
// ---------------------------------------------------------------------------

// The reply the kernel writes for make_test_dbc(), every key it writes
// present, with `edit` applied to its "dbc" object.
template<typename Edit>
static auto dbc_response(Edit edit) -> std::string {
    auto reply = Json::parse(test::parsed_dbc_response_for(test::make_test_dbc()));
    edit(reply["dbc"]);
    return reply.dump();
}

// The one signal of make_test_dbc()'s one message.
static auto signal_of(Json& dbc) -> Json& {
    return dbc["messages"][0]["signals"][0];
}

static auto dbc_error_message(std::string const& response) -> std::string {
    auto const result = detail::parse_dbc_response(response);
    REQUIRE_FALSE(result.has_value());
    CHECK(result.error().kind() == ErrorKind::Protocol);
    return std::string{result.error().message()};
}

TEST_CASE("parse_dbc_response refuses a string numerator, at the rational's place",
          "[json][parse][refusal]") {
    auto const message = dbc_error_message(dbc_response([](Json& dbc) {
        signal_of(dbc)["factor"] = Json::parse(R"({"numerator": "1", "denominator": 1})");
    }));
    CHECK(message == "reply dbc/messages/signals/factor: expected a rational, got object");
}

TEST_CASE("parse_dbc_response refuses a string varType, at its place", "[json][parse][refusal]") {
    auto const message = dbc_error_message(dbc_response([](Json& dbc) {
        dbc["environmentVars"] = Json::parse(R"([{"name": "E", "varType": "0", "initial": 0,
            "minimum": 0, "maximum": 1}])");
    }));
    CHECK(message == "reply dbc/environmentVars/varType: expected number, got string");
}

TEST_CASE("a validation refusal lacking its has_errors or issues, or holding them malformed, is "
          "refused at the place",
          "[json][parse][refusal]") {
    // The kernel writes has_errors and issues on every validation refusal, so
    // a refusal without them is the wire's fault, not a validation error.
    struct Row {
        std::string_view body;
        std::string_view refusal;
    };
    constexpr std::array rows = {
        Row{.body = R"({"status": "error", "code": "handler_validation_failed",
                        "message": "m", "has_errors": true})",
            .refusal = "reply issues: expected array, got nothing"},
        Row{.body = R"({"status": "error", "code": "handler_validation_failed",
                        "message": "m", "issues": []})",
            .refusal = "reply has_errors: expected boolean, got nothing"},
        Row{.body = R"({"status": "error", "code": "handler_validation_failed",
                        "message": "m", "has_errors": true, "issues": 5})",
            .refusal = "reply issues: expected array, got number"},
    };
    for (auto const& row : rows) {
        auto const result = detail::parse_success(row.body);
        REQUIRE_FALSE(result.has_value());
        CHECK(result.error().kind() == ErrorKind::Protocol);
        CHECK(result.error().message() == row.refusal);
    }
}

TEST_CASE("a bound refusal's triple is whole or refused at the broken place",
          "[json][parse][refusal]") {
    // A bound refusal always carries its bound_kind, observed and limit, and an
    // envelope of any code holding part of the triple holds it whole, with a
    // string field if it names one.
    struct Row {
        std::string_view body;
        std::string_view refusal;
    };
    constexpr std::array rows = {
        Row{.body = R"({"status": "error", "code": "input_bound_exceeded", "message": "m"})",
            .refusal = "reply bound_kind: expected string, got nothing"},
        Row{.body = R"({"status": "error", "code": "input_bound_exceeded", "message": "m",
              "bound_kind": 5, "observed": 1, "limit": 1})",
            .refusal = "reply bound_kind: expected string, got number"},
        Row{.body = R"({"status": "error", "code": "input_bound_exceeded", "message": "m",
              "bound_kind": "k", "limit": 1})",
            .refusal = "reply observed: expected number, got nothing"},
        Row{.body = R"({"status": "error", "code": "input_bound_exceeded", "message": "m",
              "bound_kind": "k", "observed": -1, "limit": 1})",
            .refusal = "reply observed: expected number, got number"},
        Row{.body = R"({"status": "error", "code": "input_bound_exceeded", "message": "m",
              "bound_kind": "k", "observed": 1})",
            .refusal = "reply limit: expected number, got nothing"},
        Row{.body = R"({"status": "error", "code": "input_bound_exceeded", "message": "m",
              "bound_kind": "k", "observed": 1, "limit": "x"})",
            .refusal = "reply limit: expected number, got string"},
        Row{.body = R"({"status": "error", "code": "input_bound_exceeded", "message": "m",
              "field": 5, "bound_kind": "k", "observed": 1, "limit": 1})",
            .refusal = "reply field: expected string, got number"},
        Row{.body = R"({"status": "error", "code": "handler_no_dbc", "message": "m",
              "bound_kind": "k"})",
            .refusal = "reply observed: expected number, got nothing"},
    };
    for (auto const& row : rows) {
        auto const result = detail::parse_success(row.body);
        REQUIRE_FALSE(result.has_value());
        CHECK(result.error().kind() == ErrorKind::Protocol);
        CHECK(result.error().message() == row.refusal);
    }
}

TEST_CASE("parse_dbc_response refuses a rational that is neither digits nor a pair, at its place",
          "[json][parse][refusal]") {
    struct Row {
        std::string_view factor;
        std::string_view came;
    };
    constexpr std::array rows = {
        Row{.factor = R"("1/2")", .came = "string"},
        Row{.factor = R"({"numerator": 1})", .came = "object"},
        Row{.factor = R"({"denominator": 2})", .came = "object"},
        Row{.factor = "1.5", .came = "number"},
    };
    for (auto const& row : rows) {
        auto const message = dbc_error_message(dbc_response(
            [&](Json& dbc) { signal_of(dbc)["factor"] = Json::parse(std::string{row.factor}); }));
        CHECK(message == "reply dbc/messages/signals/factor: expected a rational, got " +
                             std::string{row.came});
    }
}

TEST_CASE("parse_dbc_response refuses a multiplexed signal without its values, at their place",
          "[json][parse][refusal]") {
    auto const multiplexed = [](Json& dbc) -> Json& {
        auto& sig = signal_of(dbc);
        sig["presence"] = "multiplexed";
        sig["multiplexor"] = "Mux";
        return sig;
    };
    CHECK(dbc_error_message(dbc_response([&](Json& dbc) { multiplexed(dbc); })) ==
          "reply dbc/messages/signals/multiplex_values: expected array, got nothing");
    CHECK(dbc_error_message(dbc_response([&](Json& dbc) {
              multiplexed(dbc)["multiplex_values"] = 5;
          })) == "reply dbc/messages/signals/multiplex_values: expected array, got number");
}

TEST_CASE("parse_dbc_response reads a byte order outside the set as big endian, its last arm",
          "[json][parse]") {
    auto const result = detail::parse_dbc_response(
        dbc_response([](Json& dbc) { signal_of(dbc)["byteOrder"] = "middle_endian"; }));
    REQUIRE(result.has_value());
    CHECK(result->messages.at(0).signals.at(0).byte_order == ByteOrder::BigEndian);
}

TEST_CASE("parse_dbc_response reads a stated unsigned signal as unsigned and refuses one with no "
          "signed flag",
          "[json][parse]") {
    auto const stated = detail::parse_dbc_response(dbc_response([](Json& /*dbc*/) {}));
    REQUIRE(stated.has_value());
    CHECK_FALSE(stated->messages.at(0).signals.at(0).is_signed);
    CHECK(dbc_error_message(dbc_response([](Json& dbc) { signal_of(dbc).erase("signed"); })) ==
          "reply dbc/messages/signals/signed: expected boolean, got nothing");
}

TEST_CASE("parse_dbc_response reads an attribute's tag outside its set as the set's last arm",
          "[json][parse]") {
    // Each tag the kernel writes is one of a set it proves, so the reader
    // dispatches with no refusal of its own: the last arm reads every word the
    // arms before it do not name, and its keys are then read as that arm's.
    auto const attribute = [](std::string_view text) -> DbcAttribute {
        auto const result = detail::parse_dbc_response(dbc_response(
            [&](Json& dbc) { dbc["attributes"] = Json::array({Json::parse(std::string{text})}); }));
        REQUIRE(result.has_value());
        REQUIRE(result->attributes.size() == 1);
        return result->attributes.front();
    };

    auto const scope = std::get<DbcAttrDef>(attribute(R"({"kind": "definition", "name": "A",
        "scope": "planet", "attrType": {"kind": "int", "min": 0, "max": 1}})"));
    CHECK(scope.scope == DbcAttrScope::NodeSig);

    auto const type = std::get<DbcAttrDef>(attribute(R"({"kind": "definition", "name": "A",
        "scope": "node", "attrType": {"kind": "bogus", "min": 2, "max": 3}})"));
    auto const* const hex_type = std::get_if<DbcAttrTypeHex>(&type.attr_type);
    REQUIRE(hex_type != nullptr);
    CHECK(hex_type->min == 2);
    CHECK(hex_type->max == 3);

    auto const value = std::get<DbcAttrDefault>(
        attribute(R"({"kind": "default", "name": "A", "value": {"kind": "bogus", "value": 1}})"));
    auto const* const hex_value = std::get_if<DbcAttrValueHex>(&value.value);
    REQUIRE(hex_value != nullptr);
    CHECK(hex_value->value == 1);

    auto const target = std::get<DbcAttrAssign>(attribute(R"({"kind": "assignment", "name": "A",
        "target": {"kind": "bogus", "id": 256, "extended": false, "node": "N", "signal": "S"},
        "value": {"kind": "int", "value": 1}})"));
    auto const* const node_sig = std::get_if<DbcAttrTargetNodeSig>(&target.target);
    REQUIRE(node_sig != nullptr);
    CHECK(node_sig->node == NodeName{"N"});
    CHECK(std::get<StandardId>(node_sig->id).value() == 256);
    CHECK(node_sig->signal == "S");

    auto const kind = std::get<DbcAttrAssign>(attribute(R"({"kind": "bogus", "name": "A",
        "target": {"kind": "network"}, "value": {"kind": "int", "value": 1}})"));
    CHECK(std::holds_alternative<DbcAttrTargetNetwork>(kind.target));
}

TEST_CASE("parse_frame_response refuses a non-string reason, at its place",
          "[json][parse][refusal]") {
    auto const result = detail::parse_frame_response(
        R"({"type": "property_batch", "results": [{"type": "property", "status": "fails",
            "property_index": 0, "timestamp": 1, "reason": 5}]})");
    REQUIRE_FALSE(result.has_value());
    CHECK(result.error().message() == "reply results/reason: expected string, got number");
}

TEST_CASE("parse_frame_response refuses a results field that is not an array, at its place",
          "[json][parse][refusal]") {
    auto const result = detail::parse_frame_response(R"({"type": "property_batch", "results": 5})");
    REQUIRE_FALSE(result.has_value());
    CHECK(result.error().message() == "reply results: expected array, got number");
}

TEST_CASE("the DBC responses refuse a missing dbc field, at its place", "[json][parse][refusal]") {
    auto const parsed = detail::parse_dbc_response(R"({"status": "success"})");
    REQUIRE_FALSE(parsed.has_value());
    CHECK(parsed.error().message() == "reply dbc: expected object, got nothing");
    auto const text = detail::parse_parsed_dbc(R"({"status": "success", "warnings": []})");
    REQUIRE_FALSE(text.has_value());
    CHECK(text.error().message() == "reply dbc: expected object, got nothing");
}

TEST_CASE("parse_parsed_dbc refuses a response without warnings", "[json][parse][refusal]") {
    auto reply = Json::parse(test::parsed_dbc_response_for(test::make_test_dbc()));
    reply.erase("warnings");
    auto const result = detail::parse_parsed_dbc(reply.dump());
    REQUIRE_FALSE(result.has_value());
    CHECK(result.error().message() == "reply warnings: expected array, got nothing");
}

TEST_CASE("the issue lists read a severity outside the set as a warning, its last arm",
          "[json][parse]") {
    auto reply = Json::parse(test::parsed_dbc_response_for(test::make_test_dbc()));
    reply["warnings"] = Json::parse(R"([{"severity": "bogus", "code": "c", "detail": ""}])");
    auto const warnings = detail::parse_parsed_dbc(reply.dump());
    REQUIRE(warnings.has_value());
    REQUIRE(warnings->warnings.size() == 1);
    CHECK(warnings->warnings.front().severity == IssueSeverity::Warning);
    auto const issues = detail::parse_dbc_text_response(R"({"status": "success", "text": "",
        "issues": [{"severity": "bogus", "code": "c", "detail": ""}]})");
    REQUIRE(issues.has_value());
    REQUIRE(issues->issues.size() == 1);
    CHECK(issues->issues.front().severity == IssueSeverity::Warning);
}

TEST_CASE("parse_dbc_text_response refuses a non-string text, at its place",
          "[json][parse][refusal]") {
    auto const result = detail::parse_dbc_text_response(R"({"status": "success", "text": 5})");
    REQUIRE_FALSE(result.has_value());
    CHECK(result.error().message() == "reply text: expected string, got number");
}

TEST_CASE("parse_frame_response reads a verdict outside the set as unresolved, its last arm",
          "[json][parse]") {
    auto const result = detail::parse_frame_response(
        R"({"type": "property_batch", "results": [{"type": "property", "status": "maybe",
            "property_index": 0, "reason": "r"}]})");
    REQUIRE(result.has_value());
    auto const* batch = std::get_if<PropertyBatch>(&*result);
    REQUIRE(batch != nullptr);
    CHECK(batch->results.at(0).verdict == Verdict::Unresolved);
    CHECK(batch->results.at(0).reason == "r");
}
