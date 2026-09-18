// SPDX-FileCopyrightText: 2025 Nicolas Pelletier
// SPDX-License-Identifier: BSD-2-Clause
//
// The shared then-dispatcher of the YAML and Excel loaders: it reads the slots
// its word names from what the loader passed, and refuses a slot the loader
// did not pass by name rather than reading a filler.

#include <catch2/catch_test_macros.hpp>
#include <catch2/matchers/catch_matchers.hpp>
#include <catch2/matchers/catch_matchers_string.hpp>

#include "detail/loader_utils.hpp"

#include <aletheia/check.hpp>
#include <aletheia/enrich.hpp>
#include <aletheia/types.hpp>

#include <chrono>

using aletheia::detail::ThenSlotValues;
using aletheia::PhysicalValue;
using aletheia::Rational;
using Catch::Matchers::ContainsSubstring;

static auto then_builder() -> aletheia::ThenSignal {
    return aletheia::check::when("Brake").drops_below(PhysicalValue{Rational{10, 1}}).then("Speed");
}

static constexpr auto k_within = std::chrono::milliseconds{100};

TEST_CASE("dispatch_then reads the slot its word names", "[loader_utils]") {
    auto const builder = then_builder();
    auto const five = PhysicalValue{Rational{5, 1}};
    auto const nine = PhysicalValue{Rational{9, 1}};

    auto const rendered = [](aletheia::CheckResult const& result) {
        auto const formula = result.to_formula();
        REQUIRE(formula);
        return aletheia::format_formula(*formula);
    };
    CHECK(
        rendered(aletheia::detail::dispatch_then(builder, "equals", {{"value", five}}, k_within)) ==
        "always(not(Brake < 10) or eventually within 100ms (Speed = 5))");
    CHECK(rendered(
              aletheia::detail::dispatch_then(builder, "exceeds", {{"value", five}}, k_within)) ==
          "always(not(Brake < 10) or eventually within 100ms (Speed > 5))");
    CHECK(rendered(aletheia::detail::dispatch_then(builder, "stays_between",
                                                   {{"lo", five}, {"hi", nine}}, k_within)) ==
          "always(not(Brake < 10) or eventually within 100ms (5 <= Speed <= 9))");
}

TEST_CASE("dispatch_then refuses a slot the loader did not pass, by name", "[loader_utils]") {
    auto const builder = then_builder();
    auto const five = PhysicalValue{Rational{5, 1}};
    ThenSlotValues const range_only{{"lo", five}, {"hi", five}};
    ThenSlotValues const value_only{{"value", five}};

    CHECK_THROWS_WITH(aletheia::detail::dispatch_then(builder, "equals", range_only, k_within),
                      ContainsSubstring("'equals' reads slot 'value'"));
    CHECK_THROWS_WITH(aletheia::detail::dispatch_then(builder, "exceeds", range_only, k_within),
                      ContainsSubstring("'exceeds' reads slot 'value'"));
    CHECK_THROWS_WITH(
        aletheia::detail::dispatch_then(builder, "stays_between", value_only, k_within),
        ContainsSubstring("'stays_between' reads slot 'lo'"));
    CHECK_THROWS_WITH(aletheia::detail::dispatch_then(builder, "stays_between",
                                                      ThenSlotValues{{"lo", five}}, k_within),
                      ContainsSubstring("'stays_between' reads slot 'hi'"));
}

TEST_CASE("dispatch_then refuses a word outside the vocabulary, by name", "[loader_utils]") {
    CHECK_THROWS_WITH(aletheia::detail::dispatch_then(then_builder(), "flickers", {}, k_within),
                      ContainsSubstring("flickers"));
}
