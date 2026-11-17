// SPDX-FileCopyrightText: 2025 Nicolas Pelletier
// SPDX-License-Identifier: BSD-2-Clause
//
// The formula docs/FORMULA_RENDERING.yaml holds, built in code: every operator
// of the grammar, every predicate, a change of either sign and a time bound in
// seconds, in milliseconds and in microseconds, a binary operator the operand
// of another. The two children of every binary node differ, so a child moved,
// swapped or dropped changes the formula's wire. Each node is built from its
// alternative directly, so the formula needs no kernel to build: the tests
// that read it hold its wire and its rendering, not the kernel's check.
#pragma once

#include <aletheia/ltl.hpp>
#include <aletheia/types.hpp>

#include <memory>
#include <utility>

namespace aletheia::test {

[[nodiscard]] inline auto every_alternative() -> LtlFormula {
    using namespace ltl;
    SignalName const speed{"Speed"};
    auto const eq = atomic(Equals{.signal = speed, .value = PhysicalValue{Rational{1, 1}}});
    auto const lt = atomic(LessThan{.signal = speed, .value = PhysicalValue{Rational{3, 2}}});
    auto const gt = atomic(GreaterThan{.signal = speed, .value = PhysicalValue{Rational{7, 1}}});
    auto const le =
        atomic(LessThanOrEqual{.signal = speed, .value = PhysicalValue{Rational{220, 1}}});
    auto const ge = atomic(
        GreaterThanOrEqual{.signal = SignalName{"RPM"}, .value = PhysicalValue{Rational{0, 1}}});
    auto const bt = atomic(Between{.signal = SignalName{"Temp"},
                                   .min = PhysicalValue{Rational{-40, 1}},
                                   .max = PhysicalValue{Rational{215, 1}}});
    auto const rise =
        atomic(ChangedBy{.signal = SignalName{"Pos"}, .delta = Delta{Rational{5, 2}}});
    auto const fall =
        atomic(ChangedBy{.signal = SignalName{"Neg"}, .delta = Delta{Rational{-5, 2}}});
    auto const steady = atomic(
        StableWithin{.signal = SignalName{"Volt"}, .tolerance = Tolerance{Rational{1, 100}}});
    // always(not P) is the shape the printer writes as `never P`.
    auto never_eq = always(negate(clone(eq)));
    auto unary = both(next(clone(lt)), either(weak_next(clone(gt)), negate(clone(le))));
    auto temporal = until(always(clone(ge)), release(eventually(clone(bt)), clone(rise)));
    // Two seconds, then 1500 microseconds, which is no whole millisecond, then 7.
    auto metric_until = MetricUntil{.bound = TimeBound{2'000'000},
                                    .left = std::make_unique<LtlFormula>(clone(fall)),
                                    .right = std::make_unique<LtlFormula>(clone(steady))};
    auto metric_eventually =
        MetricEventually{.bound = TimeBound{7}, .formula = std::make_unique<LtlFormula>(clone(eq))};
    auto metric_release =
        MetricRelease{.bound = TimeBound{1'500},
                      .left = std::make_unique<LtlFormula>(std::move(metric_until)),
                      .right = std::make_unique<LtlFormula>(std::move(metric_eventually))};
    auto metric_always = MetricAlways{.bound = TimeBound{250'000},
                                      .formula = std::make_unique<LtlFormula>(clone(lt))};
    return both(both(std::move(never_eq), std::move(unary)),
                either(std::move(temporal), both(LtlFormula{std::move(metric_release)},
                                                 LtlFormula{std::move(metric_always)})));
}

} // namespace aletheia::test
