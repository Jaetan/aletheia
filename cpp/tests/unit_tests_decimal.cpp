// SPDX-FileCopyrightText: 2025 Nicolas Pelletier
// SPDX-License-Identifier: BSD-2-Clause
//
// Parity tests for Rational::from_decimal (the float principle):
// a decimal literal is parsed into an EXACT rational by the Agda kernel decimal
// SSOT (aletheia_parse_decimal), never via a float64.  Mirrors the cross-binding
// case set in python/tests/test_parse_decimal_ffi.py and the Rust/Go suites.
//
// from_decimal is RTS-gated; this lives in the unit_tests binary, which links
// tests/rts_setup_listener.cpp (it brings the GHC RTS up once per process via a
// throwaway FfiBackend), so the kernel call has a live runtime here.  The
// runtime-DOWN vocal case is covered in the dedicated
// rts_init_renderer_uninitialized_tests binary (no backend in-process).

#include <catch2/catch_test_macros.hpp>

#include <aletheia/aletheia.hpp>

#include <array>
#include <cstdint>
#include <stdexcept>
#include <string_view>
#include <utility>

using namespace aletheia;

namespace {

struct DecimalCase {
    std::string_view input;
    std::int64_t numerator;
    std::int64_t denominator;
};

// (input → exact, lowest-terms num/den).  Identical to the Python parity set.
constexpr std::array<DecimalCase, 10> kSuccessCases{{
    {"3.14", 157, 50},
    {"42", 42, 1},
    {"0.1", 1, 10},
    {"-3.14", -157, 50},
    {"0", 0, 1},
    {"-0", 0, 1},                                    // negative zero collapses to +0
    {"0.000", 0, 1},                                 // trailing-zero fraction canonicalises
    {"0.10", 1, 10},                                 // trailing zero trimmed
    {"00.1", 1, 10},                                 // leading zeros accepted
    {"9223372036854775807", 9223372036854775807, 1}, // Int64 max fits
}};

// Malformed per the grammar -?digits[.digits+]: no '+', no leading/trailing '.',
// no exponent, no fraction syntax, full consumption (trailing input rejected).
constexpr std::array<std::string_view, 10> kParseFailCases{{
    "3.14xyz",
    "1e3",
    ".5",
    "+1",
    "1/2",
    "1.",
    "1 ",
    " 1",
    "",
    "-",
}};

// A numerator or denominator beyond the Int64 wire range.
constexpr std::array<std::string_view, 2> kOverflowCases{{
    "99999999999999999999.5",
    "0.0000000000000000001",
}};

// Run from_decimal and assert it throws a Validation-kinded AletheiaException
// (user-input fault — NOT Ffi / Protocol / Core).
void expect_validation_throw(std::string_view input) {
    try {
        static_cast<void>(Rational::from_decimal(input));
        FAIL("expected Rational::from_decimal to throw for input: " << input);
    } catch (const AletheiaException& e) {
        CHECK(e.kind() == ErrorKind::Validation);
    }
}

} // namespace

TEST_CASE("Rational::from_decimal parses valid decimals to exact rationals", "[types][decimal]") {
    for (const auto& c : kSuccessCases) {
        DYNAMIC_SECTION("input=" << c.input) {
            auto r = Rational::from_decimal(c.input);
            CHECK(r.numerator() == c.numerator);
            CHECK(r.denominator() == c.denominator);
        }
    }
}

TEST_CASE("Rational::from_decimal rejects malformed literals as Validation errors",
          "[types][decimal]") {
    for (const auto& input : kParseFailCases) {
        DYNAMIC_SECTION("input=[" << input << "]") {
            expect_validation_throw(input);
        }
    }
}

TEST_CASE("Rational::from_decimal rejects int64-overflowing literals as Validation errors",
          "[types][decimal]") {
    for (const auto& input : kOverflowCases) {
        DYNAMIC_SECTION("input=" << input) {
            expect_validation_throw(input);
        }
    }
}

TEST_CASE("Rational::from_decimal rejects an interior NUL byte (cross-binding parity)",
          "[types][decimal]") {
    // An interior NUL would silently truncate a C string at the marshal boundary
    // ("1\0xyz" -> "1"), accepting a value the caller never wrote. Reject it as a
    // user-input Validation error, mirroring Rust's CString::new guard. Not in the
    // Python-mirrored set above (which uses string literals), so it is its own
    // case using an explicit embedded NUL.
    using namespace std::string_view_literals;
    expect_validation_throw("1\0xyz"sv);
}

TEST_CASE("Rational ctor/make reject out-of-int64-range integral inputs", "[types]") {
    // The non-bool-integral ctor/make accept any integral type, so a wide or
    // unsigned value outside the int64 range (here 2^63, one past INT64_MAX)
    // must be rejected before the narrowing cast rather than wrapping silently.
    constexpr std::uint64_t too_big = std::uint64_t{1} << 63U;

    SECTION("the constructor throws") {
        REQUIRE_THROWS_AS(Rational(too_big, 1), std::invalid_argument);
        REQUIRE_THROWS_AS(Rational(1, too_big), std::invalid_argument);
    }
    SECTION("make returns an error instead of a wrapped value") {
        REQUIRE_FALSE(Rational::make(too_big, 1).has_value());
        REQUIRE_FALSE(Rational::make(1, too_big).has_value());
    }
    SECTION("an in-range integral still constructs") {
        constexpr std::int64_t big_ok = std::int64_t{1} << 62; // < INT64_MAX
        REQUIRE(Rational(big_ok, 1).numerator() == big_ok);
        REQUIRE(Rational::make(big_ok, 2).has_value());
    }
}
