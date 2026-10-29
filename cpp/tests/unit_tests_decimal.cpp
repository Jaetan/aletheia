// SPDX-FileCopyrightText: 2025 Nicolas Pelletier
// SPDX-License-Identifier: BSD-2-Clause
//
// Parity tests for Rational::from_decimal (the float principle):
// a decimal literal is parsed into an EXACT rational by the Agda kernel decimal
// SSOT (aletheia_parse_decimal), never via a float64.  Mirrors the cross-binding
// case set in python/tests/test_parse_decimal_ffi.py and the Rust/Go suites.
//
// A refusal is the kernel's own Error, decoded as every kernel refusal is, and
// the literal is the caller's own text: a grammar refusal is Validation-kinded
// with its code and its position in the message, a component past the kernel's
// magnitude bound is InputBoundExceeded with the structured bound fields, and
// the shim's refusal of text it cannot hand to the kernel (a NUL byte, bytes
// that are not UTF-8) is Validation-kinded with the code FfiValidationError.
//
// from_decimal is RTS-gated; this lives in the unit_tests binary, which links
// tests/rts_setup_listener.cpp (it brings the GHC RTS up once per process via a
// throwaway FfiBackend), so the kernel call has a live runtime here.  The
// runtime-DOWN vocal case is covered in the dedicated
// rts_init_renderer_uninitialized_tests binary (no backend in-process).

#include <catch2/catch_test_macros.hpp>
#include <catch2/matchers/catch_matchers.hpp>
#include <catch2/matchers/catch_matchers_string.hpp>

#include <aletheia/aletheia.hpp>

#include <array>
#include <cstdint>
#include <format>
#include <string>
#include <string_view>

using namespace aletheia;
using Catch::Matchers::ContainsSubstring;

namespace {
struct DecimalCase {
    std::string_view input;
    std::int64_t numerator;
    std::int64_t denominator;
};

// A literal the grammar refuses, with the code the kernel answers and the
// column its message names (every refusal here is on line 1).
struct GrammarRefusal {
    std::string_view input;
    ErrorCode code;
    int column;
};

// A literal whose numerator or denominator is past the kernel's magnitude
// bound, with the magnitude the kernel measured (saturated at UINT64_MAX when
// it measured more).
struct BoundRefusal {
    std::string_view input;
    std::uint64_t observed;
};
} // namespace

// (input → exact, lowest-terms num/den).  Identical to the Python parity set.
constexpr std::array<DecimalCase, 11> k_success_cases{{
    {.input = "3.14", .numerator = 157, .denominator = 50},
    {.input = "42", .numerator = 42, .denominator = 1},
    {.input = "0.1", .numerator = 1, .denominator = 10},
    {.input = "-3.14", .numerator = -157, .denominator = 50},
    {.input = "0", .numerator = 0, .denominator = 1},
    {.input = "-0", .numerator = 0, .denominator = 1},    // negative zero collapses to +0
    {.input = "0.000", .numerator = 0, .denominator = 1}, // trailing-zero fraction canonicalises
    {.input = "0.10", .numerator = 1, .denominator = 10}, // trailing zero trimmed
    {.input = "00.1", .numerator = 1, .denominator = 10}, // leading zeros accepted
    {.input = "9223372036854775807",
     .numerator = 9223372036854775807,
     .denominator = 1}, // the magnitude bound itself fits
    {.input = "-9223372036854775807",
     .numerator = -9223372036854775807,
     .denominator = 1}, // and so does its negation
}};

// Malformed per the grammar -?digits[.digits+]: no '+', no leading/trailing '.',
// no exponent, no fraction syntax, full consumption (trailing input rejected).
// A literal whose prefix parses but leaves input behind is a trailing-input
// refusal; one no prefix of which parses is a parse failure at column 1, or at
// the column where the digits the sign promised are missing.
constexpr std::array<GrammarRefusal, 10> k_grammar_refusals{{
    {.input = "3.14xyz", .code = ErrorCode::TextTrailingInput, .column = 5},
    {.input = "1e3", .code = ErrorCode::TextTrailingInput, .column = 2},
    {.input = ".5", .code = ErrorCode::TextParseFailure, .column = 1},
    {.input = "+1", .code = ErrorCode::TextParseFailure, .column = 1},
    {.input = "1/2", .code = ErrorCode::TextTrailingInput, .column = 2},
    {.input = "1.", .code = ErrorCode::TextTrailingInput, .column = 3},
    {.input = "1 ", .code = ErrorCode::TextTrailingInput, .column = 2},
    {.input = " 1", .code = ErrorCode::TextParseFailure, .column = 1},
    {.input = "", .code = ErrorCode::TextParseFailure, .column = 1},
    {.input = "-", .code = ErrorCode::TextParseFailure, .column = 2},
}};

// A numerator or denominator past the kernel's magnitude bound.  The most
// negative Int64 is refused: its magnitude is one past the bound, which the
// kernel holds symmetrically.
constexpr std::array<BoundRefusal, 3> k_bound_refusals{{
    {.input = "99999999999999999999.5", .observed = 18446744073709551615ULL},
    {.input = "0.0000000000000000001", .observed = 10000000000000000000ULL},
    {.input = "-9223372036854775808", .observed = 9223372036854775808ULL},
}};

constexpr std::uint64_t k_magnitude_limit = 9223372036854775807ULL;

// The error from_decimal returned for `input`, each caller's section naming the
// input; the test fails where it returned a rational.
static auto refusal_of(std::string_view input) -> AletheiaError {
    auto const parsed = Rational::from_decimal(input);
    REQUIRE_FALSE(parsed.has_value());
    return parsed.error();
}

// Run from_decimal and assert the kernel refused the literal's grammar: a
// Validation-kinded error carrying the kernel's code and the position its
// message names.
static void expect_grammar_refusal(GrammarRefusal const& c) {
    auto const e = refusal_of(c.input);
    CHECK(e.kind() == ErrorKind::Validation);
    CHECK(e.code() == c.code);
    CHECK_THAT(e.text(),
               ContainsSubstring(std::format("parse failed at line 1, column {}", c.column)));
}

// Run from_decimal and assert the kernel refused a component's magnitude: an
// InputBoundExceeded error whose bound_info names the decimal field, the
// magnitude bound kind, the limit and the magnitude measured.
static void expect_bound_refusal(BoundRefusal const& c) {
    auto const e = refusal_of(c.input);
    CHECK(e.kind() == ErrorKind::InputBoundExceeded);
    CHECK(e.code() == ErrorCode::InputBoundExceeded);
    auto const& info = e.bound_info();
    REQUIRE(info.has_value());
    CHECK(info->bound_kind == bound_kind_rational_component_magnitude);
    CHECK(info->observed == c.observed);
    CHECK(info->limit == k_magnitude_limit);
    REQUIRE(info->field.has_value());
    CHECK(*info->field == "decimal");
}

// Run from_decimal and assert the shim refused the text before the kernel saw
// it: a Validation-kinded error with the code FfiValidationError and the shim's
// message.
static void expect_shim_refusal(std::string_view input, std::string_view message) {
    auto const e = refusal_of(input);
    CHECK(e.kind() == ErrorKind::Validation);
    CHECK(e.code() == ErrorCode::FfiValidationError);
    CHECK(e.text() == message);
}

TEST_CASE("Rational::from_decimal parses valid decimals to exact rationals", "[types][decimal]") {
    for (auto const& c : k_success_cases) {
        DYNAMIC_SECTION("input=" << c.input) {
            auto const r = Rational::from_decimal(c.input);
            REQUIRE(r.has_value());
            CHECK(r->numerator() == c.numerator);
            CHECK(r->denominator() == c.denominator);
        }
    }
}

TEST_CASE("Rational::from_decimal rejects malformed literals with the kernel's parse code",
          "[types][decimal]") {
    for (auto const& c : k_grammar_refusals) {
        DYNAMIC_SECTION("input=[" << c.input << "]") {
            expect_grammar_refusal(c);
        }
    }
}

TEST_CASE("Rational::from_decimal rejects a component past the magnitude bound as "
          "InputBoundExceeded",
          "[types][decimal]") {
    for (auto const& c : k_bound_refusals) {
        DYNAMIC_SECTION("input=" << c.input) {
            expect_bound_refusal(c);
        }
    }
}

TEST_CASE("Rational::from_decimal rejects an interior NUL byte (cross-binding parity)",
          "[types][decimal]") {
    // The shim reads the literal whole and refuses the NUL, rather than reading
    // "1\0xyz" as "1", a value the caller never wrote. Not in the
    // Python-mirrored set above (which uses string literals), so it is its own
    // case using an explicit embedded NUL.
    using namespace std::string_view_literals;
    expect_shim_refusal("1\0xyz"sv, "input contains a NUL byte");
}

TEST_CASE("Rational ctor/make reject out-of-int64-range integral inputs", "[types]") {
    // The non-bool-integral ctor/make accept any integral type, so a wide or
    // unsigned value outside the int64 range (here 2^63, one past INT64_MAX)
    // must be rejected before the narrowing cast rather than wrapping silently.
    constexpr std::uint64_t too_big = std::uint64_t{1} << 63U;

    SECTION("the constructor does not compile") {
        STATIC_REQUIRE_FALSE(aletheia::detail::RationalLiteral<too_big, std::uint64_t{1}>);
        STATIC_REQUIRE_FALSE(aletheia::detail::RationalLiteral<std::uint64_t{1}, too_big>);
    }
    SECTION("make returns an error instead of a wrapped value") {
        REQUIRE_FALSE(Rational::make(too_big, std::uint64_t{1}).has_value());
        REQUIRE_FALSE(Rational::make(std::uint64_t{1}, too_big).has_value());
    }
    SECTION("an in-range integral still constructs") {
        constexpr auto big_ok = static_cast<std::int64_t>(std::uint64_t{1} << 62U); // < INT64_MAX
        REQUIRE(Rational(big_ok, std::int64_t{1}).numerator() == big_ok);
        REQUIRE(Rational::make(big_ok, std::int64_t{2}).has_value());
    }
}

TEST_CASE("Rational::from_decimal rejects a non-ASCII literal as trailing input",
          "[types][decimal]") {
    // A UTF-8 literal is text the kernel reads: the digits before the euro sign
    // parse and the sign is left behind, so the refusal is the grammar's, with
    // its code and column, and never one about the bytes.
    expect_grammar_refusal(
        {.input = "1.5\xe2\x82\xac", .code = ErrorCode::TextTrailingInput, .column = 4});
}

// The input as its section is named, a byte outside printable ASCII spelled as
// an escape: a report carrying bytes that are not UTF-8 is not text, and the
// mutation lane's runner keeps no report that is not.
static auto escaped(std::string_view bytes) -> std::string {
    std::string out;
    for (auto const c : bytes) {
        if (c >= ' ' && c <= '~')
            out += c;
        else
            out += std::format("\\x{:02x}", static_cast<unsigned char>(c));
    }
    return out;
}

TEST_CASE("Rational::from_decimal rejects bytes that are not UTF-8 before the kernel reads them",
          "[types][decimal]") {
    // Each surrounds digits that are a literal without it (a stray byte, a
    // truncated sequence, an encoded surrogate, an overlong NUL), so a shim
    // that dropped what it could not decode would hand the kernel a literal.
    constexpr std::array<std::string_view, 4> not_utf8{{
        "1.5\xff",
        "1\xe2\x82.5",
        "1\xed\xa0\x80"
        "5",
        "\xc0\x80"
        "1",
    }};
    for (auto const input : not_utf8) {
        DYNAMIC_SECTION("input=[" << escaped(input) << "]") {
            expect_shim_refusal(input, "input is not valid UTF-8");
        }
    }
}
