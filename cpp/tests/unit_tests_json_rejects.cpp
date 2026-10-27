// SPDX-FileCopyrightText: 2025 Nicolas Pelletier
// SPDX-License-Identifier: BSD-2-Clause
// Unit tests: the JSON decoders' reject branches, from malformed DBC metadata
// to wire responses the verified core never emits, and the edge cases of
// the serializer and of Rational.
#include "test_helpers.hpp"

#include <catch2/catch_template_test_macros.hpp>
#include <catch2/catch_test_macros.hpp>
#include <catch2/generators/catch_generators.hpp>
#include <catch2/matchers/catch_matchers.hpp>
#include <catch2/matchers/catch_matchers_string.hpp>

#include "detail/json.hpp"
#include "required.hpp"
#include <aletheia/aletheia.hpp>
#include <aletheia/detail/checked.hpp>

#include <cstdint>
#include <functional>
#include <limits>
#include <nlohmann/json.hpp>

#include <algorithm>
#include <memory>
#include <ranges>
#include <string>
#include <type_traits>
#include <utility>
#include <variant>
#include <vector>

using aletheia::test::required;

using namespace aletheia;
using Json = nlohmann::json;
using aletheia::test::make_test_dbc;
using Catch::Matchers::ContainsSubstring;

// ===========================================================================
// Decode-validation tightening (parse_dbc_response rejects malformed
// signal/message metadata).  The base is the serializer's own output for
// make_test_dbc(), so each positive case proves well-formed core output still
// decodes; each rejection mutates exactly one field.
// ===========================================================================

static auto base_dbc_response() -> Json {
    auto const cmd = Json::parse(required(detail::serialize_parse_dbc(make_test_dbc())));
    Json resp;
    resp["status"] = "success";
    resp["dbc"] = cmd.at("dbc");
    return resp;
}

static auto first_signal(Json& resp) -> Json& {
    return resp.at("dbc").at("messages").at(0).at("signals").at(0);
}

TEST_CASE("parse_dbc_response accepts well-formed metadata", "[json][parse][dbc][validation]") {
    CHECK(detail::parse_dbc_response(base_dbc_response().dump()).has_value());
}

TEST_CASE("parse_dbc_response rejects a non-boolean extended flag",
          "[json][parse][dbc][validation]") {
    auto j = base_dbc_response();
    j.at("dbc").at("messages").at(0)["extended"] = "true";
    CHECK_FALSE(detail::parse_dbc_response(j.dump()).has_value());
}

// signal startBit 0-511 / length 1-512 (the type-level ceiling: the largest
// CAN-FD frame; per-frame fit is the kernel's entry-gate check, not the
// decoder's)
TEST_CASE("parse_dbc_response rejects out-of-range startBit/length",
          "[json][parse][dbc][validation]") {
    auto const reject = [](const char* field, int value) {
        auto j = base_dbc_response();
        first_signal(j)[field] = value;
        return !detail::parse_dbc_response(j.dump()).has_value();
    };
    auto const accept = [](const char* field, int value) {
        auto j = base_dbc_response();
        first_signal(j)[field] = value;
        return detail::parse_dbc_response(j.dump()).has_value();
    };
    CHECK(reject("startBit", 512));
    CHECK(accept("startBit", 511)); // boundary
    CHECK(reject("length", 0));
    CHECK(accept("length", 1)); // minimum valid length (lower boundary)
    CHECK(reject("length", 513));
    CHECK(accept("length", 512)); // full-frame CAN-FD boundary
}

// explicit presence discriminator (unknown / missing rejected)
TEST_CASE("parse_dbc_response rejects an unknown or missing presence",
          "[json][parse][dbc][validation]") {
    {
        auto j = base_dbc_response();
        first_signal(j)["presence"] = "sometimes";
        CHECK_FALSE(detail::parse_dbc_response(j.dump()).has_value());
    }
    {
        auto j = base_dbc_response();
        first_signal(j).erase("presence");
        CHECK_FALSE(detail::parse_dbc_response(j.dump()).has_value());
    }
}

// multiplexed presence requires non-empty multiplexor + values
TEST_CASE("parse_dbc_response rejects malformed multiplexed presence",
          "[json][parse][dbc][validation]") {
    auto const make_mux = [](const char* mux, Json values) {
        auto j = base_dbc_response();
        auto& sig = first_signal(j);
        sig["presence"] = "multiplexed";
        sig["multiplexor"] = mux;
        sig["multiplex_values"] = std::move(values);
        return j;
    };
    // empty values
    CHECK_FALSE(detail::parse_dbc_response(make_mux("Mode", Json::array()).dump()).has_value());
    // empty multiplexor
    CHECK_FALSE(detail::parse_dbc_response(make_mux("", Json::array({0})).dump()).has_value());
    // missing values
    {
        auto j = base_dbc_response();
        auto& sig = first_signal(j);
        sig["presence"] = "multiplexed";
        sig["multiplexor"] = "Mode";
        sig.erase("multiplex_values");
        CHECK_FALSE(detail::parse_dbc_response(j.dump()).has_value());
    }
    // multiplex values at and past both ends of the u32 range
    CHECK(detail::parse_dbc_response(make_mux("Mode", Json::array({4294967295LL})).dump())
              .has_value());
    for (auto const past : {std::int64_t{4294967296LL}, std::int64_t{-1}}) {
        auto const r = detail::parse_dbc_response(make_mux("Mode", Json::array({past})).dump());
        REQUIRE_FALSE(r.has_value());
        CHECK_THAT(std::string{r.error().message()},
                   ContainsSubstring("out of range (0-4294967295)"));
    }
    // well-formed multiplexed — accepted
    CHECK(detail::parse_dbc_response(make_mux("Mode", Json::array({0, 1})).dump()).has_value());
}

// ===========================================================================
// Wire-decoder reject branches, in parity with the Go and Rust suites. Each
// case drives a decoder with a malformed or unexpected wire response the
// verified core never emits, so only a direct case reaches these refusals, and
// each asserts the error kind and a message fragment so it targets its own
// branch rather than merely some failure. The coverage build
// (-DALETHEIA_COVERAGE=ON) is what shows which branches they reach.
// ===========================================================================

TEST_CASE("make_json_error rejects a missing code field", "[json][parse][error]") {
    auto const r = detail::parse_success(R"({"status": "error", "message": "m"})");
    CHECK_FALSE(r.has_value());
    CHECK(r.error().kind() == ErrorKind::Protocol);
    CHECK_THAT(std::string{r.error().message()}, ContainsSubstring("missing or non-string 'code'"));
}

TEST_CASE("make_json_error rejects a non-string code field", "[json][parse][error]") {
    auto const r = detail::parse_success(R"({"status": "error", "code": 123, "message": "m"})");
    CHECK_FALSE(r.has_value());
    CHECK_THAT(std::string{r.error().message()}, ContainsSubstring("missing or non-string 'code'"));
}

TEST_CASE("make_json_error rejects a missing message field", "[json][parse][error]") {
    auto const r = detail::parse_success(R"({"status": "error", "code": "handler_no_dbc"})");
    CHECK_FALSE(r.has_value());
    CHECK_THAT(std::string{r.error().message()},
               ContainsSubstring("missing or non-string 'message'"));
}

TEST_CASE("make_json_error rejects a non-string message field", "[json][parse][error]") {
    auto const r =
        detail::parse_success(R"({"status": "error", "code": "handler_no_dbc", "message": 123})");
    CHECK_FALSE(r.has_value());
    CHECK_THAT(std::string{r.error().message()},
               ContainsSubstring("missing or non-string 'message'"));
}

TEST_CASE("parse_rational_as_int rejects a non-numeric property_index", "[json][parse][error]") {
    auto const r = detail::parse_frame_response(
        R"({"type": "property_batch", "results": [{"status": "holds", "property_index": "x"}]})");
    CHECK_FALSE(r.has_value());
    CHECK_THAT(std::string{r.error().message()},
               ContainsSubstring("Expected integer or {numerator, denominator}"));
}

TEST_CASE("require_int rejects a fractional rational component", "[json][parse][error]") {
    auto const r = detail::parse_extraction(
        R"({"status": "success", "values": [{"name": "S", "value": {"numerator": 1.5, "denominator": 2}}]})");
    CHECK_FALSE(r.has_value());
    CHECK_THAT(std::string{r.error().message()}, ContainsSubstring("must be an integer"));
}

TEST_CASE("parse_event_ack rejects a malformed JSON envelope", "[json][parse][error]") {
    auto const r = detail::parse_event_ack("{");
    CHECK_FALSE(r.has_value());
    CHECK(r.error().kind() == ErrorKind::Protocol);
}

TEST_CASE("parse_validation lifts a status=error envelope", "[json][parse][error]") {
    auto const r = detail::parse_validation(
        R"({"status": "error", "code": "factor_zero", "message": "boom"})");
    CHECK_FALSE(r.has_value());
    CHECK(r.error().kind() == ErrorKind::Validation);
    CHECK_THAT(std::string{r.error().message()}, ContainsSubstring("boom"));
}

TEST_CASE("parse_validation rejects a wrong response type", "[json][parse][error]") {
    auto const r = detail::parse_validation(R"({"status": "weird"})");
    CHECK_FALSE(r.has_value());
    CHECK_THAT(std::string{r.error().message()}, ContainsSubstring("Expected validation response"));
}

TEST_CASE("parse_validation rejects a malformed JSON envelope", "[json][parse][error]") {
    auto const r = detail::parse_validation("{");
    CHECK_FALSE(r.has_value());
    CHECK(r.error().kind() == ErrorKind::Protocol);
}

TEST_CASE("handler_validation_failed envelope lifts issues into the typed error",
          "[json][parse][error]") {
    auto const r = detail::parse_parsed_dbc(
        R"({"status":"error","code":"handler_validation_failed",)"
        R"("message":"ParseDBCText: validation failed: Message 'M': duplicate signal name 'S'",)"
        R"("has_errors":true,"issues":[)"
        R"({"severity":"error","code":"duplicate_signal_name",)"
        R"("detail":"Message 'M': duplicate signal name 'S'"},)"
        R"({"severity":"warning","code":"offset_scale_range",)"
        R"("detail":"Signal 'S': offset/scale out of range"}]})");
    REQUIRE_FALSE(r.has_value());
    CHECK(r.error().code() == ErrorCode::HandlerValidationFailed);
    // The legacy message text is untouched by the lift.
    CHECK_THAT(std::string{r.error().message()}, ContainsSubstring("duplicate signal name 'S'"));
    REQUIRE(r.error().issues().has_value());
    auto const& issues = *r.error().issues();
    REQUIRE(issues.size() == 2);
    CHECK(issues[0].severity == IssueSeverity::Error);
    CHECK(issues[0].code == IssueCode::DuplicateSignalName);
    CHECK(issues[0].detail == "Message 'M': duplicate signal name 'S'");
    CHECK(issues[1].severity == IssueSeverity::Warning);
    CHECK(issues[1].code == IssueCode::OffsetScaleRange);
    CHECK(issues[1].detail == "Signal 'S': offset/scale out of range");
}

TEST_CASE("handler_validation_failed without structured fields degrades to nullopt",
          "[json][parse][error]") {
    // Cores predating the structured envelope emit only code/message; the
    // decode must not fail harder than before.
    auto const r =
        detail::parse_parsed_dbc(R"({"status":"error","code":"handler_validation_failed",)"
                                 R"("message":"ParseDBCText: validation failed: boom"})");
    REQUIRE_FALSE(r.has_value());
    CHECK(r.error().code() == ErrorCode::HandlerValidationFailed);
    CHECK_THAT(std::string{r.error().message()}, ContainsSubstring("boom"));
    CHECK_FALSE(r.error().issues().has_value());
}

TEST_CASE("handler_validation_failed with a malformed issues payload degrades to nullopt",
          "[json][parse][error]") {
    auto const* const envelope = GENERATE(
        // has_errors missing
        R"({"status":"error","code":"handler_validation_failed","message":"m",)"
        R"("issues":[]})",
        // has_errors ill-typed
        R"({"status":"error","code":"handler_validation_failed","message":"m",)"
        R"("has_errors":"yes","issues":[]})",
        // issues not an array
        R"({"status":"error","code":"handler_validation_failed","message":"m",)"
        R"("has_errors":true,"issues":{}})",
        // a non-object element
        R"({"status":"error","code":"handler_validation_failed","message":"m",)"
        R"("has_errors":true,"issues":[42]})",
        // an unknown severity
        R"({"status":"error","code":"handler_validation_failed","message":"m",)"
        R"("has_errors":true,"issues":[{"severity":"fatal","code":"x","detail":"d"}]})",
        // an ill-typed detail field
        R"({"status":"error","code":"handler_validation_failed","message":"m",)"
        R"("has_errors":true,"issues":[{"severity":"error","code":"x","detail":42}]})");
    auto const r = detail::parse_parsed_dbc(envelope);
    REQUIRE_FALSE(r.has_value());
    CHECK(r.error().code() == ErrorCode::HandlerValidationFailed);
    CHECK(r.error().message() == "m");
    CHECK_FALSE(r.error().issues().has_value());
}

TEST_CASE("parse_extraction lifts a status=error envelope", "[json][parse][error]") {
    auto const r =
        detail::parse_extraction(R"({"status": "error", "code": "x", "message": "boom"})");
    CHECK_FALSE(r.has_value());
    CHECK_THAT(std::string{r.error().message()}, ContainsSubstring("boom"));
}

TEST_CASE("parse_frame_data lifts a status=error envelope", "[json][parse][error]") {
    auto const r =
        detail::parse_frame_data(R"({"status": "error", "code": "x", "message": "boom"})");
    CHECK_FALSE(r.has_value());
    CHECK_THAT(std::string{r.error().message()}, ContainsSubstring("boom"));
}

TEST_CASE("parse_frame_data rejects an unexpected status", "[json][parse][error]") {
    auto const r = detail::parse_frame_data(R"({"status": "weird"})");
    CHECK_FALSE(r.has_value());
    CHECK_THAT(std::string{r.error().message()}, ContainsSubstring("Unexpected frame data status"));
}

TEST_CASE("parse_frame_response rejects a negative timestamp", "[json][parse][error]") {
    auto const r = detail::parse_frame_response(
        R"({"type": "property_batch", "results": [{"status": "holds", "property_index": 0, "timestamp": -5}]})");
    CHECK_FALSE(r.has_value());
    CHECK_THAT(std::string{r.error().message()}, ContainsSubstring("Negative timestamp"));
}

TEST_CASE("parse_frame_response lifts a status=error envelope", "[json][parse][error]") {
    auto const r =
        detail::parse_frame_response(R"({"status": "error", "code": "x", "message": "boom"})");
    CHECK_FALSE(r.has_value());
    CHECK_THAT(std::string{r.error().message()}, ContainsSubstring("boom"));
}

TEST_CASE("parse_frame_response rejects an empty property_batch", "[json][parse][error]") {
    auto const r = detail::parse_frame_response(R"({"type": "property_batch", "results": []})");
    CHECK_FALSE(r.has_value());
    CHECK_THAT(std::string{r.error().message()}, ContainsSubstring("non-empty array"));
}

TEST_CASE("parse_stream_result lifts a status=error envelope", "[json][parse][error]") {
    auto const r =
        detail::parse_stream_result(R"({"status": "error", "code": "x", "message": "boom"})");
    CHECK_FALSE(r.has_value());
    CHECK_THAT(std::string{r.error().message()}, ContainsSubstring("boom"));
}

TEST_CASE("parse_stream_result rejects a wrong response type", "[json][parse][error]") {
    auto const r = detail::parse_stream_result(R"({"status": "weird"})");
    CHECK_FALSE(r.has_value());
    CHECK_THAT(std::string{r.error().message()}, ContainsSubstring("Expected complete response"));
}

TEST_CASE("parse_stream_result rejects a warning missing property_index", "[json][parse][error]") {
    auto const r = detail::parse_stream_result(
        R"({"status": "complete", "results": [], "warnings": [{"kind": "x"}]})");
    CHECK_FALSE(r.has_value());
    CHECK_THAT(std::string{r.error().message()},
               ContainsSubstring("missing required 'property_index'"));
}

TEST_CASE("parse_stream_result rejects a negative warning property_index", "[json][parse][error]") {
    auto const r = detail::parse_stream_result(
        R"({"status": "complete", "results": [], "warnings": [{"property_index": -1}]})");
    CHECK_FALSE(r.has_value());
    CHECK_THAT(std::string{r.error().message()},
               ContainsSubstring("Negative warning property_index"));
}

TEST_CASE("parse_dbc_response lifts a status=error envelope", "[json][parse][error]") {
    auto const r =
        detail::parse_dbc_response(R"({"status": "error", "code": "x", "message": "boom"})");
    CHECK_FALSE(r.has_value());
    CHECK_THAT(std::string{r.error().message()}, ContainsSubstring("boom"));
}

// format_dbc_text response decoder — decode-level coverage of the success arm and
// its malformed branches (the real-FFI integration tests never emit these).
TEST_CASE("parse_dbc_text_response decodes a success response with issues", "[json][parse]") {
    auto const r = detail::parse_dbc_text_response(
        R"({"status":"success","text":"VERSION \"\"\n","issues":[{"severity":"warning","code":"multi_value_mux_selector","detail":"mux"}]})");
    REQUIRE(r.has_value());
    CHECK(r->text == "VERSION \"\"\n");
    REQUIRE(r->issues.size() == 1);
    CHECK(r->issues[0].severity == IssueSeverity::Warning);
    CHECK(r->issues[0].code == IssueCode::MultiValueMuxSelector);
    CHECK(r->issues[0].code_raw == "multi_value_mux_selector");
    CHECK(r->issues[0].detail == "mux");
}

TEST_CASE("parse_dbc_text_response defaults an absent issues field to empty", "[json][parse]") {
    auto const r = detail::parse_dbc_text_response(R"({"status":"success","text":"x"})");
    REQUIRE(r.has_value());
    CHECK(r->text == "x");
    CHECK(r->issues.empty());
}

TEST_CASE("parse_dbc_text_response rejects a non-array issues field", "[json][parse][error]") {
    // Parity with Python/Go/Rust: a present-but-non-array issues on a success
    // response is a protocol error, not silently harvested from an object's values.
    auto const r =
        detail::parse_dbc_text_response(R"({"status":"success","text":"x","issues":{}})");
    CHECK_FALSE(r.has_value());
    CHECK_THAT(std::string{r.error().message()}, ContainsSubstring("'issues' must be an array"));
}

TEST_CASE("parse_dbc_text_response rejects an unexpected status", "[json][parse][error]") {
    auto const r = detail::parse_dbc_text_response(R"({"status":"weird"})");
    CHECK_FALSE(r.has_value());
    CHECK_THAT(std::string{r.error().message()},
               ContainsSubstring("Unexpected formatDBCText response status"));
}

TEST_CASE("parse_dbc_text_response rejects a missing text field", "[json][parse][error]") {
    auto const r = detail::parse_dbc_text_response(R"({"status":"success"})");
    CHECK_FALSE(r.has_value());
    CHECK_THAT(std::string{r.error().message()}, ContainsSubstring("Missing or non-string 'text'"));
}

TEST_CASE("DbcDefinition unresolvedValueDescs keeps an extended CAN ID across serialize -> parse",
          "[json][serialize][parse][dbc]") {
    auto dbc = make_test_dbc();
    dbc.unresolved_value_descs.push_back(DbcRawValueDesc{
        .can_id = CanId{*ExtendedId::create(0x18FEF100)},
        .signal_name = "Phantom",
        .entries = {DbcValueEntry{.value = 0, .description = "Off"}},
    });

    auto const cmd_str = required(detail::serialize_parse_dbc(dbc));
    auto cmd_j = Json::parse(cmd_str);
    REQUIRE(cmd_j["dbc"]["unresolvedValueDescs"].size() == 1);
    CHECK(cmd_j["dbc"]["unresolvedValueDescs"][0]["extended"] == true);

    const Json response = {{"status", "success"}, {"dbc", cmd_j["dbc"]}};
    auto const parsed = detail::parse_dbc_response(response.dump());
    REQUIRE(parsed.has_value());
    REQUIRE(parsed->unresolved_value_descs.size() == 1);
    auto const& rvd = parsed->unresolved_value_descs[0];
    REQUIRE(std::holds_alternative<ExtendedId>(rvd.can_id));
    CHECK(std::get<ExtendedId>(rvd.can_id).value() == 0x18FEF100);
}

TEST_CASE("serialize_set_properties refuses a formula nested past the depth bound",
          "[json][serialize][bounds]") {
    // Nesting to the bound is accepted and one level more is refused here
    // rather than on the wire, whichever operand the depth descends through:
    // the unary operand, or the left or the right operand of a binary one.
    // Every alternative that carries a formula is its own serializer
    // instantiation, so each is nested on its own: the unary ones through their
    // operand, the binary ones through the left and through the right.
    using Wrap = std::function<LtlFormula(LtlFormula, LtlFormula)>;
    auto const us = Timestamp{1};
    // The generator is built once and serves its alternatives on the later
    // entries of this body, each of them a fresh frame, so an alternative
    // holds nothing by reference: the two helpers below are captured by value
    // where they are used, as the bound is.
    auto const metric_until = [us](LtlFormula left, LtlFormula right) {
        return LtlFormula{MetricUntil{.bound = us,
                                      .left = std::make_unique<LtlFormula>(std::move(left)),
                                      .right = std::make_unique<LtlFormula>(std::move(right))}};
    };
    auto const metric_release = [us](LtlFormula left, LtlFormula right) {
        return LtlFormula{MetricRelease{.bound = us,
                                        .left = std::make_unique<LtlFormula>(std::move(left)),
                                        .right = std::make_unique<LtlFormula>(std::move(right))}};
    };
    auto const wrap = GENERATE_COPY(
        Wrap{[](LtlFormula f, LtlFormula) { return ltl::next(std::move(f)); }},
        Wrap{[](LtlFormula f, LtlFormula) { return ltl::weak_next(std::move(f)); }},
        Wrap{[](LtlFormula f, LtlFormula) { return ltl::always(std::move(f)); }},
        Wrap{[](LtlFormula f, LtlFormula) { return ltl::eventually(std::move(f)); }},
        Wrap{[](LtlFormula f, LtlFormula) { return ltl::negate(std::move(f)); }},
        Wrap{[us](LtlFormula f, LtlFormula) { return ltl::within(us, std::move(f)); }},
        Wrap{[us](LtlFormula f, LtlFormula) { return ltl::always_within(us, std::move(f)); }},
        Wrap{
            [](LtlFormula f, LtlFormula leaf) { return ltl::both(std::move(f), std::move(leaf)); }},
        Wrap{
            [](LtlFormula f, LtlFormula leaf) { return ltl::both(std::move(leaf), std::move(f)); }},
        Wrap{[](LtlFormula f, LtlFormula leaf) {
            return ltl::either(std::move(f), std::move(leaf));
        }},
        Wrap{[](LtlFormula f, LtlFormula leaf) {
            return ltl::either(std::move(leaf), std::move(f));
        }},
        Wrap{[](LtlFormula f, LtlFormula leaf) {
            return ltl::until(std::move(f), std::move(leaf));
        }},
        Wrap{[](LtlFormula f, LtlFormula leaf) {
            return ltl::until(std::move(leaf), std::move(f));
        }},
        Wrap{[](LtlFormula f, LtlFormula leaf) {
            return ltl::release(std::move(f), std::move(leaf));
        }},
        Wrap{[](LtlFormula f, LtlFormula leaf) {
            return ltl::release(std::move(leaf), std::move(f));
        }},
        Wrap{[metric_until](LtlFormula f, LtlFormula leaf) {
            return metric_until(std::move(f), std::move(leaf));
        }},
        Wrap{[metric_until](LtlFormula f, LtlFormula leaf) {
            return metric_until(std::move(leaf), std::move(f));
        }},
        Wrap{[metric_release](LtlFormula f, LtlFormula leaf) {
            return metric_release(std::move(f), std::move(leaf));
        }},
        Wrap{[metric_release](LtlFormula f, LtlFormula leaf) {
            return metric_release(std::move(leaf), std::move(f));
        }});
    auto const nest = [&wrap](std::uint64_t depth) {
        auto const leaf = [] {
            return ltl::atomic(ltl::equals(SignalName{"S"}, PhysicalValue{Rational{1, 1}}));
        };
        auto f = leaf();
        std::ranges::for_each(std::views::repeat(0, depth),
                              [&](auto) { f = wrap(std::move(f), leaf()); });
        std::vector<LtlFormula> props;
        props.push_back(std::move(f));
        return props;
    };
    CHECK(detail::serialize_set_properties(nest(max_nesting_depth)).has_value());
    auto const deep = detail::serialize_set_properties(nest(max_nesting_depth + 1));
    CHECK(detail::error_of(deep).kind() == ErrorKind::Validation);
    CHECK(detail::error_of(deep).message() == "Formula nesting depth exceeds 64");
}

TEST_CASE("a rational whose numerator is INT64_MIN is emitted raw, as a pair",
          "[json][serialize][rational]") {
    // The numerator cannot be normalised, since its absolute value does not
    // exist; the wire carries it un-normalised rather than the serializer
    // computing it.
    constexpr auto lowest = std::numeric_limits<std::int64_t>::min();
    std::vector<LtlFormula> props;
    props.push_back(ltl::atomic(ltl::equals(SignalName{"S"}, PhysicalValue{Rational{lowest, 1}})));
    auto const j = Json::parse(required(detail::serialize_set_properties(props)));
    auto const& value = j.at("properties").at(0).at("predicate").at("value");
    REQUIRE(value.is_object());
    CHECK(value.at("numerator") == lowest);
    CHECK(value.at("denominator") == 1);
}

// The constructor and make are templates over the integral types, so each
// width and signedness a caller uses is its own instantiation, and each must
// refuse the zero and admit the one on its own: the constructor as a literal
// that does not compile, make as an error. A signed one also refuses the
// negative; an unsigned one has none to refuse.
// The two arguments are separate template parameters, so a caller that mixes
// a wide numerator with a narrow literal denominator instantiates a pair of
// its own, which refuses the zero like every other pair.
TEST_CASE("Rational refuses a non-positive denominator when its arguments differ in type",
          "[rational]") {
    STATIC_CHECK_FALSE(aletheia::detail::RationalLiteral<std::int64_t{1}, 0>);
    CHECK_FALSE(Rational::make(std::int64_t{1}, 0).has_value());
    CHECK(Rational::make(std::int64_t{1}, 1).has_value());
    STATIC_CHECK_FALSE(aletheia::detail::RationalLiteral<1, std::uint64_t{0}>);
    CHECK_FALSE(Rational::make(1, std::uint64_t{0}).has_value());
}

TEMPLATE_TEST_CASE("Rational refuses a non-positive denominator on both construction paths",
                   "[rational]", short, int, long, long long, unsigned short, unsigned,
                   unsigned long, unsigned long long) {
    using T = TestType;
    STATIC_CHECK_FALSE(aletheia::detail::RationalLiteral<T{1}, T{0}>);
    CHECK(Rational(T{1}, T{1}).denominator() == 1);
    CHECK_FALSE(Rational::make(T{1}, T{0}).has_value());
    CHECK(Rational::make(T{1}, T{1}).has_value());
    if constexpr (std::is_signed_v<T>) {
        STATIC_CHECK_FALSE(aletheia::detail::RationalLiteral<T{1}, T{-1}>);
        CHECK_FALSE(Rational::make(T{1}, T{-1}).has_value());
    }
}

TEST_CASE("an integer field past the signed 64-bit range is refused by its width",
          "[json][parse][bounds]") {
    // The largest unsigned value takes the unsigned branch of the reader,
    // where the signed one would wrap it to minus one and accept it.
    auto const big = detail::parse_extraction(R"({
        "status": "success",
        "values": [{"name": "S", "value": {"numerator": 18446744073709551615, "denominator": 1}}],
        "errors": [], "absent": []
    })");
    REQUIRE_FALSE(big.has_value());
    CHECK_THAT(std::string{big.error().message()}, ContainsSubstring("out of range"));
    auto const var = detail::parse_dbc_response(R"({
        "status": "success",
        "dbc": {"version": "1.0", "messages": [],
                "environmentVars": [{"name": "Wide", "varType": 18446744073709551615,
                                     "initial": 0, "minimum": 0, "maximum": 0}]}
    })");
    REQUIRE_FALSE(var.has_value());
    CHECK_THAT(std::string{var.error().message()}, ContainsSubstring("varType is out of range"));
}
