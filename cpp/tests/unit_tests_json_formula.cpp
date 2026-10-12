// SPDX-FileCopyrightText: 2025 Nicolas Pelletier
// SPDX-License-Identifier: BSD-2-Clause
// Unit tests: format_formula, the pretty-printer violation enrichment uses
// to render a failed formula into a human-readable string.
#include <catch2/catch_test_macros.hpp>

#include <aletheia/aletheia.hpp>
#include <aletheia/enrich.hpp>

#include <memory>

using namespace aletheia;

// ===========================================================================
// Formula pretty-printer tests (format_formula)
// ===========================================================================

TEST_CASE("format_formula always less than", "[enrich]") {
    auto const f = ltl::always(
        ltl::atomic(ltl::less_than(SignalName{"Speed"}, PhysicalValue{Rational{220, 1}})));
    CHECK(format_formula(f) == "always(Speed < 220)");
}

TEST_CASE("format_formula never pattern", "[enrich]") {
    auto const f =
        ltl::never(ltl::greater_than(SignalName{"Speed"}, PhysicalValue{Rational{100, 1}}));
    CHECK(format_formula(f) == "never Speed > 100");
}

TEST_CASE("format_formula eventually", "[enrich]") {
    auto const f = ltl::eventually(
        ltl::atomic(ltl::equals(SignalName{"Mode"}, PhysicalValue{Rational{1, 1}})));
    CHECK(format_formula(f) == "eventually(Mode = 1)");
}

TEST_CASE("format_formula metric always", "[enrich]") {
    auto const f = ltl::always_within(
        Timestamp{5'000'000},
        ltl::atomic(ltl::less_than(SignalName{"Speed"}, PhysicalValue{Rational{220, 1}})));
    CHECK(format_formula(f) == "always within 5s (Speed < 220)");
}

TEST_CASE("format_formula metric eventually", "[enrich]") {
    auto const f =
        ltl::within(Timestamp{2'000'000},
                    ltl::atomic(ltl::equals(SignalName{"Mode"}, PhysicalValue{Rational{1, 1}})));
    CHECK(format_formula(f) == "eventually within 2s (Mode = 1)");
}

TEST_CASE("format_formula next", "[enrich]") {
    auto const f = ltl::next(
        ltl::atomic(ltl::less_than(SignalName{"Speed"}, PhysicalValue{Rational{220, 1}})));
    CHECK(format_formula(f) == "next(Speed < 220)");
}

TEST_CASE("format_formula and", "[enrich]") {
    auto const f = ltl::both(
        ltl::atomic(ltl::less_than(SignalName{"Speed"}, PhysicalValue{Rational{220, 1}})),
        ltl::atomic(ltl::greater_than(SignalName{"RPM"}, PhysicalValue{Rational{500, 1}})));
    CHECK(format_formula(f) == "Speed < 220 and RPM > 500");
}

TEST_CASE("format_formula or", "[enrich]") {
    auto const f = ltl::either(
        ltl::atomic(ltl::less_than(SignalName{"Speed"}, PhysicalValue{Rational{220, 1}})),
        ltl::atomic(ltl::greater_than(SignalName{"RPM"}, PhysicalValue{Rational{500, 1}})));
    CHECK(format_formula(f) == "Speed < 220 or RPM > 500");
}

TEST_CASE("format_formula until", "[enrich]") {
    auto const f =
        ltl::until(ltl::atomic(ltl::less_than(SignalName{"Speed"}, PhysicalValue{Rational{50, 1}})),
                   ltl::atomic(ltl::equals(SignalName{"Brake"}, PhysicalValue{Rational{1, 1}})));
    CHECK(format_formula(f) == "Speed < 50 until Brake = 1");
}

TEST_CASE("format_formula release", "[enrich]") {
    auto const f =
        ltl::release(ltl::atomic(ltl::equals(SignalName{"A"}, PhysicalValue{Rational{1, 1}})),
                     ltl::atomic(ltl::equals(SignalName{"B"}, PhysicalValue{Rational{}})));
    CHECK(format_formula(f) == "A = 1 release B = 0");
}

TEST_CASE("implies desugars to or(not(antecedent), consequent)", "[enrich]") {
    auto const ante = [] {
        return ltl::atomic(ltl::less_than(SignalName{"Speed"}, PhysicalValue{Rational{50, 1}}));
    };
    auto const cons = [] {
        return ltl::atomic(ltl::greater_than(SignalName{"RPM"}, PhysicalValue{Rational{500, 1}}));
    };
    // implies(a, c) is the standard LTL encoding !a || c — identical to
    // either(negate(a), c), matching Go's Implies, Rust's Formula::implies, and
    // Python's .implies(). Asserted structurally via the printer, no literal string.
    CHECK(format_formula(ltl::implies(ante(), cons())) ==
          format_formula(ltl::either(ltl::negate(ante()), cons())));
}

TEST_CASE("format_formula all predicate types", "[enrich]") {
    auto const eq = ltl::atomic(ltl::equals(SignalName{"S"}, PhysicalValue{Rational{42, 1}}));
    CHECK(format_formula(eq) == "S = 42");

    auto const lt = ltl::atomic(ltl::less_than(SignalName{"S"}, PhysicalValue{Rational{10, 1}}));
    CHECK(format_formula(lt) == "S < 10");

    auto const gt = ltl::atomic(ltl::greater_than(SignalName{"S"}, PhysicalValue{Rational{5, 1}}));
    CHECK(format_formula(gt) == "S > 5");

    auto const le =
        ltl::atomic(ltl::less_than_or_equal(SignalName{"S"}, PhysicalValue{Rational{100, 1}}));
    CHECK(format_formula(le) == "S <= 100");

    auto const ge =
        ltl::atomic(ltl::greater_than_or_equal(SignalName{"S"}, PhysicalValue{Rational{}}));
    CHECK(format_formula(ge) == "S >= 0");

    auto const bw = ltl::atomic(ltl::between(SignalName{"S"}, PhysicalValue{Rational{10, 1}},
                                             PhysicalValue{Rational{29, 2}}));
    CHECK(format_formula(bw) == "10 <= S <= 14.5");

    auto const cb = ltl::atomic(ltl::changed_by(SignalName{"S"}, Delta{Rational{5, 1}}));
    CHECK(format_formula(cb) == "\xce\x94S >= 5");

    auto const cb_neg = ltl::atomic(ltl::changed_by(SignalName{"S"}, Delta{Rational{-3, 1}}));
    CHECK(format_formula(cb_neg) == "\xce\x94S <= -3");

    auto const sw = ltl::atomic(ltl::stable_within(SignalName{"S"}, Tolerance{Rational{2, 1}}));
    CHECK(format_formula(sw) == "|\xce\x94S| <= 2");
}

TEST_CASE("format_formula metric until", "[enrich]") {
    using namespace std::chrono_literals;
    auto const f = LtlFormula{MetricUntil{
        .bound = Timestamp{3'000'000},
        .left = std::make_unique<LtlFormula>(
            ltl::atomic(ltl::less_than(SignalName{"Speed"}, PhysicalValue{Rational{50, 1}}))),
        .right = std::make_unique<LtlFormula>(
            ltl::atomic(ltl::equals(SignalName{"Brake"}, PhysicalValue{Rational{1, 1}})))}};
    CHECK(format_formula(f) == "Speed < 50 until within 3s Brake = 1");
}

TEST_CASE("format_formula metric release", "[enrich]") {
    using namespace std::chrono_literals;
    auto const f = LtlFormula{
        MetricRelease{.bound = Timestamp{500'000},
                      .left = std::make_unique<LtlFormula>(
                          ltl::atomic(ltl::equals(SignalName{"A"}, PhysicalValue{Rational{1, 1}}))),
                      .right = std::make_unique<LtlFormula>(
                          ltl::atomic(ltl::equals(SignalName{"B"}, PhysicalValue{Rational{}})))}};
    CHECK(format_formula(f) == "A = 1 release within 500ms B = 0");
}
