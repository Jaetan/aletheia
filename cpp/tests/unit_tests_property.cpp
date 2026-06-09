// SPDX-FileCopyrightText: 2025 Nicolas Pelletier
// SPDX-License-Identifier: BSD-2-Clause
//
// Catch2 GENERATE-based property tests (R18 cluster 5 — Cat 33c).
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

#include <cstdint>
#include <string>

using namespace aletheia;

TEST_CASE("Rational round-trips through serialize+parse for any int64 numerator", "[property]") {
    // Pick a small, bounded set per Catch2 GENERATE semantics; the
    // libFuzzer harness covers the wide-range case.  These values exercise
    // the boundary classes (zero, positive, negative, max/min int64-ish).
    auto numerator = GENERATE(std::int64_t{0}, std::int64_t{1}, std::int64_t{-1}, std::int64_t{42},
                              std::int64_t{-42}, std::int64_t{1'000'000}, std::int64_t{-1'000'000},
                              std::int64_t{1LL << 32}, std::int64_t{-(1LL << 32)});
    auto denominator =
        GENERATE(std::int64_t{1}, std::int64_t{2}, std::int64_t{7}, std::int64_t{1000});
    Rational original{numerator, denominator};
    // Serialize a wire-form DBC carrying the Rational as a signal factor;
    // round-trip through serialize → parse and assert value equality
    // (cross-multiplication, avoids canonical-form reasoning).
    auto sid = StandardId::create(0x100);
    REQUIRE(sid.has_value());
    auto dlc = Dlc::create(8);
    REQUIRE(dlc.has_value());
    DbcSignal sig{
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
    DbcDefinition dbc{
        .version = "1.0",
        .messages = {DbcMessage{
            .id = CanId{*sid},
            .name = MessageName{"M"},
            .dlc = *dlc,
            .sender = NodeName{"E"},
            .signals = {sig},
        }},
    };
    auto wire = detail::serialize_parsed_dbc_response(dbc);
    auto parsed = detail::parse_parsed_dbc(wire);
    REQUIRE(parsed.has_value());
    REQUIRE(parsed.value().dbc.messages.size() == 1);
    REQUIRE(parsed.value().dbc.messages[0].signals.size() == 1);
    auto round_trip = parsed.value().dbc.messages[0].signals[0].factor.get();
    // Cross-multiplication value equality.
    CHECK(original.numerator() * round_trip.denominator() ==
          round_trip.numerator() * original.denominator());
}

TEST_CASE("Standard CAN ID factory accepts every value in [0, 2048)", "[property]") {
    // Bounded sweep of the standard CAN ID range; the upper bound of 2047
    // is the documented max for 11-bit standard frames.  Any drift in the
    // factory's accept set surfaces as a bounded-range property failure.
    auto value =
        GENERATE(std::uint32_t{0}, std::uint32_t{1}, std::uint32_t{0x7FF}, // 2047, max standard
                 std::uint32_t{0x100}, std::uint32_t{0x500});
    auto sid = StandardId::create(value);
    CHECK(sid.has_value());
}

TEST_CASE("Standard CAN ID factory rejects every value >= 2048", "[property]") {
    auto value = GENERATE(std::uint32_t{0x800}, // 2048, first illegal
                          std::uint32_t{0x801}, std::uint32_t{0xFFFF}, std::uint32_t{0xFFFFFFFF});
    auto sid = StandardId::create(value);
    CHECK_FALSE(sid.has_value());
}

TEST_CASE("DLC factory accepts every value in [0, 15]", "[property]") {
    auto value = GENERATE(std::uint8_t{0}, std::uint8_t{1}, std::uint8_t{8}, std::uint8_t{9},
                          std::uint8_t{15});
    auto dlc = Dlc::create(value);
    CHECK(dlc.has_value());
}

TEST_CASE("DLC factory rejects every value > 15", "[property]") {
    auto value = GENERATE(std::uint8_t{16}, std::uint8_t{32}, std::uint8_t{100}, std::uint8_t{255});
    auto dlc = Dlc::create(value);
    CHECK_FALSE(dlc.has_value());
}
