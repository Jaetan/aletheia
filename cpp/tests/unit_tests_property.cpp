// SPDX-FileCopyrightText: 2025 Nicolas Pelletier
// SPDX-License-Identifier: BSD-2-Clause
//
// Catch2 GENERATE-based property tests.
// Counterpart of go property_test.go and python tests/test_property_*.py.
//
// Round-trip + parity properties over generated input ranges.  Catch2's
// GENERATE produces statically-bounded sequences (small enough to ship in
// every test run); larger ranges live in the libFuzzer harnesses under
// tests/fuzz/.  These properties focus on logical invariants that fuzzers
// alone cannot express ("should not panic" → "must round-trip exactly").

#include <catch2/catch_test_macros.hpp>
#include <catch2/generators/catch_generators.hpp>
#include <catch2/generators/catch_generators_range.hpp>

#include "../src/detail/json.hpp"

#include <aletheia/dbc.hpp>
#include <aletheia/types.hpp>

#include "u128_testing.hpp"

#include <cstdint>
#include <limits>
#include <string>

using namespace aletheia;

using Magnitude = unsigned __int128;

// The kernel's magnitude bound, 2^128-1.
constexpr auto k_largest = std::numeric_limits<Magnitude>::max();

TEST_CASE("Rational round-trips through serialize+parse for magnitudes to 2^128-1", "[property]") {
    // Pick a small, bounded set per Catch2 GENERATE semantics; the
    // libFuzzer harness covers the wide-range case.  These values exercise
    // the boundary classes: zero, small, past 32 and 64 bits, and the kernel's
    // magnitude bound, 2^128-1, on either sign.
    auto const negative = GENERATE(false, true);
    auto const numerator =
        GENERATE(Magnitude{0}, Magnitude{1}, Magnitude{42}, Magnitude{1'000'000},
                 Magnitude{1} << 32U, Magnitude{1} << 63U, Magnitude{1} << 64U, k_largest);
    auto const denominator =
        GENERATE(Magnitude{1}, Magnitude{7}, Magnitude{1000}, (Magnitude{1} << 64U) + 1, k_largest);
    auto const original = Rational::make(negative, numerator, denominator).value();
    // Serialize a wire-form DBC carrying the Rational as a signal factor and
    // round-trip it through serialize -> parse: every Rational is stored
    // reduced, so the value comes back equal.
    auto const sid = StandardId::create(0x100);
    REQUIRE(sid.has_value());
    auto const dlc = Dlc::create(8);
    REQUIRE(dlc.has_value());
    DbcSignal const sig{
        .name = SignalName{"S"},
        .start_bit = BitPosition{0},
        .bit_length = BitLength{16},
        .byte_order = ByteOrder::LittleEndian,
        .is_signed = false,
        .factor = RationalFactor{original},
        .offset = RationalOffset{Rational{0, 1}},
        .minimum = RationalBound{Rational{0, 1}},
        .maximum = RationalBound{Rational{1, 1}},
        .unit = Unit{""},
        .presence = AlwaysPresent{},
    };
    DbcDefinition const dbc{
        .version = "1.0",
        .messages = {DbcMessage{
            .id = CanId{*sid},
            .name = MessageName{"M"},
            .dlc = *dlc,
            .sender = NodeName{"E"},
            .signals = {sig},
        }},
    };
    auto const wire = detail::serialize_parsed_dbc_response(dbc);
    auto const parsed = detail::parse_parsed_dbc(wire);
    REQUIRE(parsed.has_value());
    REQUIRE(parsed.value().dbc.messages.size() == 1);
    REQUIRE(parsed.value().dbc.messages[0].signals.size() == 1);
    CHECK(parsed.value().dbc.messages[0].signals[0].factor.get() == original);
}

TEST_CASE("Standard CAN ID factory accepts every value in [0, 2048)", "[property]") {
    // Exhaustive over the whole standard range rather than a sample, since the
    // range is small enough to sweep: any hole in the factory's accept set is
    // a failure here, not a sampling miss.
    auto const value = GENERATE(range(0, 2048));
    auto const sid = StandardId::create(static_cast<std::uint32_t>(value));
    CHECK(sid.has_value());
}

TEST_CASE("Standard CAN ID factory rejects values from 2048 up", "[property]") {
    // The rejected side spans the whole 32-bit range, so this one samples: the
    // first illegal value, its successor, and two far above it.
    auto const value =
        GENERATE(std::uint32_t{0x800}, // 2048, first illegal
                 std::uint32_t{0x801}, std::uint32_t{0xFFFF}, std::uint32_t{0xFFFFFFFF});
    auto const sid = StandardId::create(value);
    CHECK_FALSE(sid.has_value());
}

TEST_CASE("DLC factory accepts every value in [0, 15]", "[property]") {
    // The code's whole legal range, swept.
    auto const value = GENERATE(range(0, 16));
    auto const dlc = Dlc::create(static_cast<std::uint8_t>(value));
    CHECK(dlc.has_value());
}

TEST_CASE("DLC factory rejects every value > 15", "[property]") {
    // The argument is a byte, so the rejected side is swept too: every value
    // from the first illegal one to the largest the type holds.
    auto const value = GENERATE(range(16, 256));
    auto const dlc = Dlc::create(static_cast<std::uint8_t>(value));
    CHECK_FALSE(dlc.has_value());
}
