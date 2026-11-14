// SPDX-FileCopyrightText: 2025 Nicolas Pelletier
// SPDX-License-Identifier: BSD-2-Clause
//
// The 128-bit JSON reader and writer: every value the reader is handed lands
// where its text puts it, a whole number is held in the node its sign and
// magnitude call for, and the writer writes each node as `Json::dump` would,
// a negative number past -2^127 as its digits.

#include <catch2/catch_test_macros.hpp>

#include "detail/wide_json.hpp"
#include "u128_testing.hpp"
#include <aletheia/types.hpp>

#include <limits>
#include <string>
#include <string_view>

using aletheia::detail::dump_json;
using aletheia::detail::Json;
using aletheia::detail::json_of;
using aletheia::detail::parse_json;
using aletheia::detail::sign_magnitude_of;
using aletheia::detail::uint128_of;
using aletheia::SignMagnitude;

namespace {

// 2^127, the magnitude of the most negative signed 128-bit integer.
constexpr auto signed_magnitude_max = static_cast<unsigned __int128>(1) << 127U;
constexpr std::string_view most_negative_signed = "-170141183460469231731687303715884105728";
constexpr std::string_view past_most_negative = "-170141183460469231731687303715884105729";

} // namespace

TEST_CASE("every value a parse reads lands where its text puts it", "[wide_json]") {
    CHECK(parse_json("[null]") == Json::array({nullptr}));
    // The inner array closes before the 2, which is the outer array's.
    CHECK(parse_json("[[1],2]") == Json::array({Json::array({1}), 2}));
}

TEST_CASE("a negative number down to -2^127 is held signed and one past it as its magnitude",
          "[wide_json]") {
    auto const most_negative = parse_json(most_negative_signed);
    CHECK(most_negative.is_number_integer());
    CHECK(most_negative == Json(std::numeric_limits<__int128>::min()));
    CHECK(json_of(true, signed_magnitude_max).is_number_integer());
    CHECK(json_of(true, signed_magnitude_max) == most_negative);
    auto const past = parse_json(past_most_negative);
    CHECK(past.is_binary());
    CHECK(sign_magnitude_of(past) ==
          SignMagnitude{.negative = true, .magnitude = signed_magnitude_max + 1});
    CHECK(json_of(true, signed_magnitude_max + 1) == past);
}

TEST_CASE("uint128_of reads a whole number that is not negative and nothing else", "[wide_json]") {
    CHECK(uint128_of(parse_json("7")) == static_cast<unsigned __int128>(7));
    CHECK(uint128_of(parse_json("340282366920938463463374607431768211455")) ==
          std::numeric_limits<unsigned __int128>::max());
    // A signed node holding a value that is not negative: -0 read from text,
    // and a value a caller built from a signed integer.
    CHECK(uint128_of(parse_json("-0")) == static_cast<unsigned __int128>(0));
    CHECK(uint128_of(Json(static_cast<__int128>(5))) == static_cast<unsigned __int128>(5));
    CHECK_FALSE(uint128_of(parse_json("-1")).has_value());
    CHECK_FALSE(uint128_of(parse_json(past_most_negative)).has_value());
    CHECK_FALSE(uint128_of(Json(2.5)).has_value());
}

TEST_CASE("sign_magnitude_of reads a whole number's sign and magnitude and nothing else",
          "[wide_json]") {
    CHECK(sign_magnitude_of(parse_json("7")) == SignMagnitude{.negative = false, .magnitude = 7});
    CHECK(sign_magnitude_of(parse_json("340282366920938463463374607431768211455")) ==
          SignMagnitude{.negative = false,
                        .magnitude = std::numeric_limits<unsigned __int128>::max()});
    CHECK(sign_magnitude_of(parse_json("-0")) == SignMagnitude{.negative = false, .magnitude = 0});
    CHECK(sign_magnitude_of(parse_json("-1")) == SignMagnitude{.negative = true, .magnitude = 1});
    CHECK_FALSE(sign_magnitude_of(Json(2.5)).has_value());
}

TEST_CASE("a binary node is a number only under its subtype and at its width", "[wide_json]") {
    // The 16 bytes of 2^127+1, the least significant first.
    Json::binary_t::container_type bytes(16);
    bytes.front() = 1;
    bytes.back() = 0x80;
    CHECK(sign_magnitude_of(Json::binary(bytes, 1)) ==
          SignMagnitude{.negative = true, .magnitude = signed_magnitude_max + 1});
    CHECK_FALSE(sign_magnitude_of(Json::binary(bytes)).has_value());
    CHECK_FALSE(sign_magnitude_of(Json::binary(bytes, 2)).has_value());
    bytes.pop_back();
    CHECK_FALSE(sign_magnitude_of(Json::binary(bytes, 1)).has_value());
}

TEST_CASE("dump_json writes a negative number past -2^127 as its digits in any container",
          "[wide_json]") {
    auto const past = json_of(true, signed_magnitude_max + 1);
    CHECK(dump_json(past) == past_most_negative);
    CHECK(dump_json(Json::array({past})) == "[" + std::string{past_most_negative} + "]");
    CHECK(dump_json(Json{{"a", past}}) == R"({"a":)" + std::string{past_most_negative} + "}");
    // A value that is no container is the serializer's to write.
    CHECK(dump_json(json_of(false, 1)) == "1");
}

// The writer walks the containers itself, so each kind is indented one step
// past the container around it. The two kinds are held by separate cases,
// each with the other kind outside.
TEST_CASE("a pretty dump indents an object one step past the array around it", "[wide_json]") {
    CHECK(dump_json(parse_json(R"([{"a":1}])"), 2) == "[\n  {\n    \"a\": 1\n  }\n]");
}

TEST_CASE("a pretty dump indents an array one step past the object around it", "[wide_json]") {
    CHECK(dump_json(parse_json(R"({"a":[1]})"), 2) == "{\n  \"a\": [\n    1\n  ]\n}");
}

TEST_CASE("a pretty dump writes an empty container as its two brackets", "[wide_json]") {
    CHECK(dump_json(parse_json("[{},[]]"), 2) == "[\n  {},\n  []\n]");
}

TEST_CASE("a zero indent writes each member on a line of its own", "[wide_json]") {
    CHECK(dump_json(parse_json(R"({"a":[1]})"), 0) == "{\n\"a\": [\n1\n]\n}");
}
