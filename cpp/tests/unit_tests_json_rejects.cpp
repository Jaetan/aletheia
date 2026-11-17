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
#include "detail/wide_json.hpp"
#include "required.hpp"
#include "u128_testing.hpp"
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
#include <string_view>
#include <type_traits>
#include <utility>
#include <variant>
#include <vector>

using aletheia::test::required;

using namespace aletheia;
using Json = nlohmann::json;
using aletheia::test::make_test_dbc;
using Catch::Matchers::ContainsSubstring;
using Catch::Matchers::StartsWith;

// The refusal parse_dbc_response answers for `reply`.
static auto dbc_refusal(std::string const& reply) -> std::string {
    auto const result = detail::parse_dbc_response(reply);
    REQUIRE_FALSE(result.has_value());
    CHECK(result.error().kind() == ErrorKind::Protocol);
    return std::string{result.error().message()};
}

// ===========================================================================
// parse_dbc_response refuses malformed signal and message places. The base is
// the serializer's own output for make_test_dbc(), so each positive case
// proves well-formed core output still decodes; each refusal mutates exactly
// one field.
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
    CHECK(dbc_refusal(j.dump()) == "reply dbc/messages/extended: expected boolean, got string");
}

// The presence is required and one of "always" and "multiplexed", any other
// word refused at its place, though the signal carries a multiplexor and its
// selector values.
TEST_CASE("parse_dbc_response rejects an unknown or missing presence",
          "[json][parse][dbc][validation]") {
    auto const refused = [](Json word) {
        auto j = base_dbc_response();
        auto& sig = first_signal(j);
        sig["presence"] = std::move(word);
        sig["multiplexor"] = "Mode";
        sig["multiplex_values"] = Json::array({2});
        return dbc_refusal(j.dump());
    };
    CHECK(refused("bogus_word") == R"(reply dbc/messages/signals/presence: expected "always" or )"
                                   R"("multiplexed", got "bogus_word")");
    CHECK(refused(0) ==
          R"(reply dbc/messages/signals/presence: expected "always" or "multiplexed", got number)");
    {
        auto j = base_dbc_response();
        first_signal(j).erase("presence");
        CHECK(dbc_refusal(j.dump()) == R"(reply dbc/messages/signals/presence: expected "always" )"
                                       R"(or "multiplexed", got nothing)");
    }
}

// A multiplexed presence carries its multiplexor and its selector values, each
// value a whole number to 2^128-1.
TEST_CASE("parse_dbc_response rejects malformed multiplexed presence",
          "[json][parse][dbc][validation]") {
    // The values are written into the reply as text, so a value past what
    // nlohmann::json holds reaches the reader as written.
    auto const make_mux = [](std::string_view values) {
        auto j = detail::parse_json(base_dbc_response().dump());
        auto& sig = j.at("dbc").at("messages").at(0).at("signals").at(0);
        sig["presence"] = "multiplexed";
        sig["multiplexor"] = "Mode";
        sig["multiplex_values"] = detail::parse_json(values);
        return detail::dump_json(j);
    };
    // missing values
    {
        auto j = base_dbc_response();
        auto& sig = first_signal(j);
        sig["presence"] = "multiplexed";
        sig["multiplexor"] = "Mode";
        sig.erase("multiplex_values");
        CHECK(dbc_refusal(j.dump()) ==
              "reply dbc/messages/signals/multiplex_values: expected array, got nothing");
    }
    // the largest value is read exactly; a negative one, or one past 2^128-1,
    // is refused
    auto const largest =
        detail::parse_dbc_response(make_mux("[340282366920938463463374607431768211455]"));
    REQUIRE(largest.has_value());
    auto const& presence = largest->messages.at(0).signals.at(0).presence;
    REQUIRE(std::holds_alternative<Multiplexed>(presence));
    CHECK(std::get<Multiplexed>(presence).multiplex_values ==
          std::vector{MultiplexValue{std::numeric_limits<unsigned __int128>::max()}});
    for (auto const* const past : {"[340282366920938463463374607431768211456]", "[-1]"})
        CHECK(dbc_refusal(make_mux(past)) ==
              "reply dbc/messages/signals/multiplex_values: expected number, got number");
    // well-formed multiplexed, accepted
    CHECK(detail::parse_dbc_response(make_mux("[0, 1]")).has_value());
}

// ===========================================================================
// Wire-decoder reject branches, in parity with the Go and Rust suites. Each
// case drives a decoder with a malformed or unexpected wire response the
// verified core never emits, so only a direct case reaches these refusals, and
// each asserts the error kind and a message fragment so it targets its own
// branch rather than merely some failure. The coverage build
// (-DALETHEIA_COVERAGE=ON) is what shows which branches they reach.
// ===========================================================================

TEST_CASE("an error envelope rejects a missing message field", "[json][parse][error]") {
    auto const r = detail::parse_success(R"({"status": "error", "code": "handler_no_dbc"})");
    REQUIRE_FALSE(r.has_value());
    CHECK(r.error().message() == "reply message: expected string, got nothing");
}

TEST_CASE("an error envelope rejects a non-string message field", "[json][parse][error]") {
    auto const r =
        detail::parse_success(R"({"status": "error", "code": "handler_no_dbc", "message": 123})");
    REQUIRE_FALSE(r.has_value());
    CHECK(r.error().message() == "reply message: expected string, got number");
}

TEST_CASE("parse_frame_response rejects a non-numeric property_index", "[json][parse][error]") {
    auto const r = detail::parse_frame_response(
        R"({"type": "property_batch", "results": [{"type": "property", "status": "holds",
            "property_index": "x"}]})");
    REQUIRE_FALSE(r.has_value());
    CHECK(r.error().message() == "reply results/property_index: expected number, got string");
}

TEST_CASE("parse_event_ack rejects a malformed JSON envelope", "[json][parse][error]") {
    auto const r = detail::parse_event_ack("{");
    REQUIRE_FALSE(r.has_value());
    CHECK(r.error().kind() == ErrorKind::Protocol);
    CHECK_THAT(std::string{r.error().message()}, StartsWith("reply: expected JSON text, got "));
}

TEST_CASE("parse_validation lifts a status=error envelope", "[json][parse][error]") {
    auto const r = detail::parse_validation(
        R"({"status": "error", "code": "handler_no_dbc", "message": "boom"})");
    REQUIRE_FALSE(r.has_value());
    CHECK(r.error().kind() == ErrorKind::Validation);
    CHECK(r.error().message() == "boom");
}

TEST_CASE("parse_validation rejects a wrong response type", "[json][parse][error]") {
    auto const r = detail::parse_validation(R"({"status": "weird"})");
    REQUIRE_FALSE(r.has_value());
    CHECK(r.error().message() == R"(reply status: expected "validation" or "error", got "weird")");
}

TEST_CASE("parse_validation rejects a malformed JSON envelope", "[json][parse][error]") {
    auto const r = detail::parse_validation("{");
    REQUIRE_FALSE(r.has_value());
    CHECK(r.error().kind() == ErrorKind::Protocol);
    CHECK_THAT(std::string{r.error().message()}, StartsWith("reply: expected JSON text, got "));
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
    // The message text is untouched by the lift.
    CHECK(r.error().message() ==
          "ParseDBCText: validation failed: Message 'M': duplicate signal name 'S'");
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

TEST_CASE("handler_validation_failed with a missing or malformed issues payload is refused at "
          "its place",
          "[json][parse][error]") {
    // The kernel writes has_errors and issues on every validation refusal, so
    // an envelope without them, or holding them malformed, is the wire's
    // fault: a Protocol error, not the validation refusal.
    auto const [envelope, refusal] = GENERATE(table<char const*, char const*>({
        {R"({"status":"error","code":"handler_validation_failed","message":"m"})",
         "reply has_errors: expected boolean, got nothing"},
        {R"({"status":"error","code":"handler_validation_failed","message":"m",)"
         R"("issues":[]})",
         "reply has_errors: expected boolean, got nothing"},
        {R"({"status":"error","code":"handler_validation_failed","message":"m",)"
         R"("has_errors":"yes","issues":[]})",
         "reply has_errors: expected boolean, got string"},
        {R"({"status":"error","code":"handler_validation_failed","message":"m",)"
         R"("has_errors":true,"issues":{}})",
         "reply issues: expected array, got object"},
        {R"({"status":"error","code":"handler_validation_failed","message":"m",)"
         R"("has_errors":true,"issues":[42]})",
         "reply issues: expected object, got number"},
        {R"({"status":"error","code":"handler_validation_failed","message":"m",)"
         R"("has_errors":true,"issues":[{"severity":"error","code":"factor_zero","detail":42}]})",
         "reply issues/detail: expected string, got number"},
    }));
    auto const r = detail::parse_parsed_dbc(envelope);
    REQUIRE_FALSE(r.has_value());
    CHECK(r.error().kind() == ErrorKind::Protocol);
    CHECK_FALSE(r.error().code().has_value());
    CHECK(r.error().message() == refusal);
}

TEST_CASE("parse_extraction lifts a status=error envelope", "[json][parse][error]") {
    auto const r = detail::parse_extraction(
        R"({"status": "error", "code": "handler_no_dbc", "message": "boom"})");
    REQUIRE_FALSE(r.has_value());
    CHECK(r.error().message() == "boom");
}

TEST_CASE("parse_frame_data lifts a status=error envelope", "[json][parse][error]") {
    auto const r = detail::parse_frame_data(
        R"({"status": "error", "code": "handler_no_dbc", "message": "boom"})");
    CHECK_FALSE(r.has_value());
    CHECK_THAT(std::string{r.error().message()}, ContainsSubstring("boom"));
}

TEST_CASE("parse_frame_data rejects an unexpected status", "[json][parse][error]") {
    auto const r = detail::parse_frame_data(R"({"status": "weird"})");
    REQUIRE_FALSE(r.has_value());
    CHECK(r.error().message() == R"(reply status: expected "success" or "error", got "weird")");
}

TEST_CASE("parse_frame_response rejects a negative timestamp", "[json][parse][error]") {
    auto const r = detail::parse_frame_response(
        R"({"type": "property_batch", "results": [{"type": "property", "status": "fails",
            "property_index": 0, "timestamp": -5, "reason": "r"}]})");
    REQUIRE_FALSE(r.has_value());
    CHECK(r.error().message() == "reply results/timestamp: expected number, got number");
}

TEST_CASE("parse_frame_response lifts a status=error envelope", "[json][parse][error]") {
    auto const r = detail::parse_frame_response(
        R"({"status": "error", "code": "handler_no_dbc", "message": "boom"})");
    CHECK_FALSE(r.has_value());
    CHECK_THAT(std::string{r.error().message()}, ContainsSubstring("boom"));
}

TEST_CASE("parse_stream_result lifts a status=error envelope", "[json][parse][error]") {
    auto const r = detail::parse_stream_result(
        R"({"status": "error", "code": "handler_no_dbc", "message": "boom"})");
    CHECK_FALSE(r.has_value());
    CHECK_THAT(std::string{r.error().message()}, ContainsSubstring("boom"));
}

TEST_CASE("parse_stream_result rejects a wrong response type", "[json][parse][error]") {
    auto const r = detail::parse_stream_result(R"({"status": "weird"})");
    REQUIRE_FALSE(r.has_value());
    CHECK(r.error().message() == R"(reply status: expected "complete" or "error", got "weird")");
}

TEST_CASE("parse_stream_result rejects a warning missing property_index", "[json][parse][error]") {
    auto const r = detail::parse_stream_result(
        R"({"status": "complete", "results": [], "warnings": [{"kind": "uncached_atom",
            "detail": "d"}]})");
    REQUIRE_FALSE(r.has_value());
    CHECK(r.error().message() == "reply warnings/property_index: expected number, got nothing");
}

TEST_CASE("parse_stream_result rejects a negative warning property_index", "[json][parse][error]") {
    auto const r = detail::parse_stream_result(
        R"({"status": "complete", "results": [], "warnings": [{"kind": "uncached_atom",
            "property_index": -1, "detail": "d"}]})");
    REQUIRE_FALSE(r.has_value());
    CHECK(r.error().message() == "reply warnings/property_index: expected number, got number");
}

TEST_CASE("parse_stream_result reads the uncached_atom kind as the one WarningKind names",
          "[json][parse]") {
    auto const r = detail::parse_stream_result(
        R"({"status": "complete", "results": [], "warnings": [{"kind": "uncached_atom",
            "property_index": 3, "detail": "d"}]})");
    REQUIRE(r.has_value());
    REQUIRE(r->warnings.size() == 1);
    CHECK(r->warnings[0].kind == WarningKind::UncachedAtom);
    CHECK(r->warnings[0].property_index == PropertyIndex{3});
    CHECK(r->warnings[0].detail == "d");
}

TEST_CASE("parse_dbc_response lifts a status=error envelope", "[json][parse][error]") {
    auto const r = detail::parse_dbc_response(
        R"({"status": "error", "code": "handler_no_dbc", "message": "boom"})");
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
    CHECK(r->issues[0].detail == "mux");
}

TEST_CASE("parse_dbc_text_response rejects an absent issues field", "[json][parse][error]") {
    // The kernel writes the issues of every text, none included.
    auto const r = detail::parse_dbc_text_response(R"({"status":"success","text":"x"})");
    REQUIRE_FALSE(r.has_value());
    CHECK(r.error().message() == "reply issues: expected array, got nothing");
}

TEST_CASE("parse_dbc_text_response rejects a non-array issues field", "[json][parse][error]") {
    // Parity with Python/Go/Rust: a present-but-non-array issues on a success
    // response is a protocol error, not silently harvested from an object's values.
    auto const r =
        detail::parse_dbc_text_response(R"({"status":"success","text":"x","issues":{}})");
    REQUIRE_FALSE(r.has_value());
    CHECK(r.error().message() == "reply issues: expected array, got object");
}

TEST_CASE("parse_dbc_text_response rejects an unexpected status", "[json][parse][error]") {
    auto const r = detail::parse_dbc_text_response(R"({"status":"weird"})");
    REQUIRE_FALSE(r.has_value());
    CHECK(r.error().message() == R"(reply status: expected "success" or "error", got "weird")");
}

TEST_CASE("parse_dbc_text_response rejects a missing text field", "[json][parse][error]") {
    auto const r = detail::parse_dbc_text_response(R"({"status":"success"})");
    REQUIRE_FALSE(r.has_value());
    CHECK(r.error().message() == "reply text: expected string, got nothing");
}

TEST_CASE("DbcDefinition unresolvedValueDescs keeps an extended CAN ID across serialize -> parse",
          "[json][serialize][parse][dbc]") {
    auto dbc = make_test_dbc();
    dbc.unresolved_value_descs.push_back(DbcRawValueDesc{
        .can_id = CanId{*ExtendedId::create(0x18FEF100)},
        .signal_name = "Phantom",
        .entries = {DbcValueEntry{.value = SignMagnitude{}, .description = "Off"}},
    });

    auto const cmd_str = required(detail::serialize_parse_dbc(dbc));
    auto cmd_j = Json::parse(cmd_str);
    REQUIRE(cmd_j["dbc"]["unresolvedValueDescs"].size() == 1);
    CHECK(cmd_j["dbc"]["unresolvedValueDescs"][0]["extended"] == true);

    Json const response = {{"status", "success"}, {"dbc", cmd_j["dbc"]}};
    auto const parsed = detail::parse_dbc_response(response.dump());
    REQUIRE(parsed.has_value());
    REQUIRE(parsed->unresolved_value_descs.size() == 1);
    auto const& rvd = parsed->unresolved_value_descs[0];
    REQUIRE(std::holds_alternative<ExtendedId>(rvd.can_id));
    CHECK(std::get<ExtendedId>(rvd.can_id).value() == 0x18FEF100);
}

// The metric operators the nesting test wraps a formula in, each at a bound of
// one microsecond: the bounded eventually and always of one operand, and the
// bounded until and release of two.
constexpr auto nesting_bound = TimeBound{1};

static auto metric_eventually(LtlFormula f) -> LtlFormula {
    return LtlFormula{MetricEventually{.bound = nesting_bound,
                                       .formula = std::make_unique<LtlFormula>(std::move(f))}};
}

static auto metric_always(LtlFormula f) -> LtlFormula {
    return LtlFormula{MetricAlways{.bound = nesting_bound,
                                   .formula = std::make_unique<LtlFormula>(std::move(f))}};
}

static auto metric_until(LtlFormula left, LtlFormula right) -> LtlFormula {
    return LtlFormula{MetricUntil{.bound = nesting_bound,
                                  .left = std::make_unique<LtlFormula>(std::move(left)),
                                  .right = std::make_unique<LtlFormula>(std::move(right))}};
}

static auto metric_release(LtlFormula left, LtlFormula right) -> LtlFormula {
    return LtlFormula{MetricRelease{.bound = nesting_bound,
                                    .left = std::make_unique<LtlFormula>(std::move(left)),
                                    .right = std::make_unique<LtlFormula>(std::move(right))}};
}

TEST_CASE("serialize_set_properties refuses a formula nested past the depth bound",
          "[json][serialize][bounds]") {
    // Nesting to the bound is accepted and one level more is refused here
    // rather than on the wire, whichever operand the depth descends through:
    // the unary operand, or the left or the right operand of a binary one.
    // Every alternative that carries a formula is its own serializer
    // instantiation, so each is nested on its own: the unary ones through their
    // operand, the binary ones through the left and through the right. No
    // alternative captures anything, so each holds nothing of the frame the
    // generator was built in.
    using Wrap = std::function<LtlFormula(LtlFormula, LtlFormula)>;
    auto const wrap =
        GENERATE(Wrap{[](LtlFormula f, LtlFormula) { return ltl::next(std::move(f)); }},
                 Wrap{[](LtlFormula f, LtlFormula) { return ltl::weak_next(std::move(f)); }},
                 Wrap{[](LtlFormula f, LtlFormula) { return ltl::always(std::move(f)); }},
                 Wrap{[](LtlFormula f, LtlFormula) { return ltl::eventually(std::move(f)); }},
                 Wrap{[](LtlFormula f, LtlFormula) { return ltl::negate(std::move(f)); }},
                 Wrap{[](LtlFormula f, LtlFormula) { return metric_eventually(std::move(f)); }},
                 Wrap{[](LtlFormula f, LtlFormula) { return metric_always(std::move(f)); }},
                 Wrap{[](LtlFormula f, LtlFormula leaf) {
                     return ltl::both(std::move(f), std::move(leaf));
                 }},
                 Wrap{[](LtlFormula f, LtlFormula leaf) {
                     return ltl::both(std::move(leaf), std::move(f));
                 }},
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
                 Wrap{[](LtlFormula f, LtlFormula leaf) {
                     return metric_until(std::move(f), std::move(leaf));
                 }},
                 Wrap{[](LtlFormula f, LtlFormula leaf) {
                     return metric_until(std::move(leaf), std::move(f));
                 }},
                 Wrap{[](LtlFormula f, LtlFormula leaf) {
                     return metric_release(std::move(f), std::move(leaf));
                 }},
                 Wrap{[](LtlFormula f, LtlFormula leaf) {
                     return metric_release(std::move(leaf), std::move(f));
                 }});
    auto const nest = [&wrap](std::uint64_t depth) {
        auto const leaf = [] {
            return ltl::atomic(
                Equals{.signal = SignalName{"S"}, .value = PhysicalValue{Rational{1, 1}}});
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

TEST_CASE("a rational whose magnitudes reach 2^128-1 is written exactly",
          "[json][serialize][rational]") {
    // A whole number is written as its signed digits and any other as the
    // {numerator, denominator} object, each magnitude whole to 128 bits.
    constexpr auto largest = std::numeric_limits<unsigned __int128>::max();
    auto const written = [](Rational value) {
        std::vector<LtlFormula> props;
        props.push_back(
            ltl::atomic(Equals{.signal = SignalName{"S"}, .value = PhysicalValue{value}}));
        return detail::parse_json(required(detail::serialize_set_properties(props)))
            .at("properties")
            .at(0)
            .at("predicate")
            .at("value");
    };
    CHECK(detail::sign_magnitude_of(
              written(Rational::integer(std::numeric_limits<std::int64_t>::min()))) ==
          SignMagnitude{.negative = true, .magnitude = static_cast<unsigned __int128>(1) << 63U});
    CHECK(detail::sign_magnitude_of(written(required(Rational::make(true, largest, 1)))) ==
          SignMagnitude{.negative = true, .magnitude = largest});
    // Two consecutive whole numbers share no factor, so the pair is reduced.
    auto const fraction = written(required(Rational::make(true, largest, largest - 1)));
    REQUIRE(fraction.is_object());
    CHECK(detail::sign_magnitude_of(fraction.at("numerator")) ==
          SignMagnitude{.negative = true, .magnitude = largest});
    CHECK(detail::sign_magnitude_of(fraction.at("denominator")) ==
          SignMagnitude{.negative = false, .magnitude = largest - 1});
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

TEST_CASE("a rational's components are read whole to 2^128-1 and refused past it",
          "[json][parse][bounds]") {
    auto const extracted = [](std::string_view numerator, std::string_view denominator) {
        return detail::parse_extraction(
            R"({"status": "success", "values": [{"name": "S", "value": {"numerator": )" +
            std::string{numerator} + R"(, "denominator": )" + std::string{denominator} +
            R"(}}], "errors": [], "absent": []})");
    };
    constexpr auto largest = std::numeric_limits<unsigned __int128>::max();
    auto const whole = extracted("-340282366920938463463374607431768211455",
                                 "340282366920938463463374607431768211454");
    REQUIRE(whole.has_value());
    REQUIRE(whole->values.size() == 1);
    auto const& value = whole->values[0].value.get();
    CHECK(value.negative());
    CHECK(value.numerator() == largest);
    CHECK(value.denominator() == largest - 1);
    for (auto const& [numerator, denominator] :
         {std::pair{"340282366920938463463374607431768211456", "1"},
          std::pair{"1", "340282366920938463463374607431768211456"}}) {
        auto const past = extracted(numerator, denominator);
        REQUIRE_FALSE(past.has_value());
        CHECK(past.error().message() == "reply values/value: expected a rational, got object");
    }
}
