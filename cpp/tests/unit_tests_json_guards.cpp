// SPDX-FileCopyrightText: 2025 Nicolas Pelletier
// SPDX-License-Identifier: BSD-2-Clause
// Unit tests: each place of a reply refused in the one form the four bindings
// share, and each tag word outside its set refused at its place.
#include <catch2/catch_test_macros.hpp>

#include "detail/json.hpp"
#include "test_helpers.hpp"
#include <aletheia/aletheia.hpp>

#include <nlohmann/json.hpp>

#include <array>
#include <format>
#include <functional>
#include <string>
#include <string_view>
#include <utility>
#include <vector>

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

TEST_CASE("parse_dbc_response reads a byte order as its word and refuses any other at its place",
          "[json][parse][refusal]") {
    for (auto const& [word, order] : std::to_array<std::pair<std::string_view, ByteOrder>>(
             {{"little_endian", ByteOrder::LittleEndian}, {"big_endian", ByteOrder::BigEndian}})) {
        auto const result = detail::parse_dbc_response(
            dbc_response([&](Json& dbc) { signal_of(dbc)["byteOrder"] = std::string{word}; }));
        REQUIRE(result.has_value());
        CHECK(result->messages.at(0).signals.at(0).byte_order == order);
    }
    CHECK(dbc_error_message(dbc_response([](Json& dbc) {
              signal_of(dbc)["byteOrder"] = "bogus_word";
          })) == R"(reply dbc/messages/signals/byteOrder: expected "little_endian" or )"
                 R"("big_endian", got "bogus_word")");
    CHECK(dbc_error_message(dbc_response([](Json& dbc) { signal_of(dbc)["byteOrder"] = 0; })) ==
          R"(reply dbc/messages/signals/byteOrder: expected "little_endian" or "big_endian", )"
          R"(got number)");
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

// What a reader answered: the message of the error it returned, or "accepted".
template<typename T>
static auto answer(Result<T> const& result) -> std::string {
    return result ? std::string{"accepted"} : std::string{result.error().message()};
}

// A reader of a reply holding one entry, the entry's JSON text.
using EntryReader = std::function<std::string(std::string const&)>;

namespace {

// A reader and the place of the key its entries break.
struct PlacedReader {
    std::string place;
    EntryReader read;
};

// One entry a reader is fed and what came at the place it breaks.
struct Arrival {
    std::string entry;
    std::string came;
};

} // namespace

// Each reply holding validation issues, with the place of an issue's `key`,
// and the reader taking it: a validation, a parsed DBC's warnings, a refused
// load's envelope and a DBC text's issues.
static auto issue_readers(std::string_view key) -> std::vector<PlacedReader> {
    auto const dbc =
        Json::parse(test::parsed_dbc_response_for(test::make_test_dbc())).at("dbc").dump();
    return {
        {.place = std::format("issues/{}", key),
         .read =
             [](std::string const& issue) {
                 return answer(detail::parse_validation(
                     R"({"status":"validation","has_errors":false,"issues":[)" + issue + "]}"));
             }},
        {.place = std::format("warnings/{}", key),
         .read =
             [dbc](std::string const& issue) {
                 return answer(detail::parse_parsed_dbc(R"({"status":"success","dbc":)" + dbc +
                                                        R"(,"warnings":[)" + issue + "]}"));
             }},
        {.place = std::format("issues/{}", key),
         .read =
             [](std::string const& issue) {
                 return std::string{
                     detail::binary_refusal(
                         R"({"status":"error","code":"handler_validation_failed","message":"m",)"
                         R"("has_errors":true,"issues":[)" +
                             issue + "]}",
                         ErrorKind::Validation)
                         .message()};
             }},
        {.place = std::format("issues/{}", key),
         .read =
             [](std::string const& issue) {
                 return answer(detail::parse_dbc_text_response(
                     R"({"status":"success","text":"VERSION \"\"\n","issues":[)" + issue + "]}"));
             }},
    };
}

// What each reader answers for each arrival, beside the refusal at its place
// expecting `expected`, every row compared at once so a failure shows each
// row's answer.
static void check_refusals(std::vector<PlacedReader> const& readers, std::string_view expected,
                           std::vector<Arrival> const& arrivals) {
    std::vector<std::string> answers;
    std::vector<std::string> refusals;
    for (auto const& [place, read] : readers) {
        for (auto const& [entry, came] : arrivals) {
            answers.push_back(read(entry));
            refusals.push_back(std::format("reply {}: expected {}, got {}", place, expected, came));
        }
    }
    CHECK(answers == refusals);
}

TEST_CASE("a severity outside error and warning is refused at its place",
          "[json][parse][refusal]") {
    check_refusals(
        issue_readers("severity"), R"("error" or "warning")",
        {
            {.entry = R"({"severity":"fatal","code":"factor_zero","detail":"d"})",
             .came = R"("fatal")"},
            {.entry = R"({"code":"factor_zero","detail":"d"})", .came = "nothing"},
            {.entry = R"({"severity":0,"code":"factor_zero","detail":"d"})", .came = "number"},
        });
}

TEST_CASE("an issue code outside the issue codes is refused at its place",
          "[json][parse][refusal]") {
    check_refusals(
        issue_readers("code"), "an issue code",
        {
            {.entry = R"({"severity":"warning","code":"some_future_code","detail":"d"})",
             .came = R"("some_future_code")"},
            {.entry = R"({"severity":"warning","detail":"d"})", .came = "nothing"},
            {.entry = R"({"severity":"warning","code":0,"detail":"d"})", .came = "number"},
        });
}

TEST_CASE("an error code outside the error codes is refused at its place",
          "[json][parse][refusal]") {
    // The binary entries' envelope reader and a command's reply reader.
    check_refusals(
        {
            {.place = "code",
             .read =
                 [](std::string const& reply) {
                     return std::string{
                         detail::binary_refusal(reply, ErrorKind::Protocol).message()};
                 }},
            {.place = "code",
             .read =
                 [](std::string const& reply) { return answer(detail::parse_validation(reply)); }},
        },
        "an error code",
        {
            {.entry = R"({"status":"error","code":"c","message":"m"})", .came = R"("c")"},
            {.entry = R"({"status":"error","message":"m"})", .came = "nothing"},
            {.entry = R"({"status":"error","code":0,"message":"m"})", .came = "number"},
        });
}

TEST_CASE("parse_dbc_text_response refuses a non-string text, at its place",
          "[json][parse][refusal]") {
    auto const result = detail::parse_dbc_text_response(R"({"status": "success", "text": 5})");
    REQUIRE_FALSE(result.has_value());
    CHECK(result.error().message() == "reply text: expected string, got number");
}

// The two replies holding property results, with the place of a result's
// `key`: a frame's batch and the end of a stream.
static auto result_readers(std::string_view key) -> std::vector<PlacedReader> {
    auto const place = std::format("results/{}", key);
    return {
        {.place = place,
         .read =
             [](std::string const& result) {
                 return answer(detail::parse_frame_response(
                     R"({"type":"property_batch","results":[)" + result + "]}"));
             }},
        {.place = place,
         .read =
             [](std::string const& result) {
                 return answer(detail::parse_stream_result(R"({"status":"complete","results":[)" +
                                                           result + R"(],"warnings":[]})"));
             }},
    };
}

TEST_CASE("a result type other than property is refused at its place", "[json][parse][refusal]") {
    check_refusals(
        result_readers("type"), R"("property")",
        {
            {.entry = R"({"type":"verdict","status":"holds","property_index":0})",
             .came = R"("verdict")"},
            {.entry = R"({"status":"holds","property_index":0})", .came = "nothing"},
            {.entry = R"({"type":0,"status":"holds","property_index":0})", .came = "number"},
        });
}

TEST_CASE("a result status outside fails, holds and unresolved is refused at its place",
          "[json][parse][refusal]") {
    check_refusals(
        result_readers("status"), R"("fails", "holds" or "unresolved")",
        {
            {.entry = R"({"type":"property","status":"bogus","property_index":0,"reason":"r"})",
             .came = R"("bogus")"},
            {.entry = R"({"type":"property","property_index":0,"reason":"r"})", .came = "nothing"},
            {.entry = R"({"type":"property","status":0,"property_index":0,"reason":"r"})",
             .came = "number"},
        });
}

TEST_CASE("a stream warning kind other than uncached_atom is refused at its place",
          "[json][parse][refusal]") {
    check_refusals(
        {{.place = "warnings/kind",
          .read =
              [](std::string const& warning) {
                  return answer(detail::parse_stream_result(
                      R"({"status":"complete","results":[],"warnings":[)" + warning + "]}"));
              }}},
        R"("uncached_atom")",
        {
            {.entry = R"({"kind":"stale_atom","property_index":0,"detail":"d"})",
             .came = R"("stale_atom")"},
            {.entry = R"({"property_index":0,"detail":"d"})", .came = "nothing"},
            {.entry = R"({"kind":0,"property_index":0,"detail":"d"})", .came = "number"},
        });
}
