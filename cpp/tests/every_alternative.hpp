// SPDX-FileCopyrightText: 2025 Nicolas Pelletier
// SPDX-License-Identifier: BSD-2-Clause
//
// The formula docs/FORMULA_RENDERING.yaml holds, built in code: every operator
// of the grammar, every predicate, a change of either sign and a time bound in
// seconds, in milliseconds and in microseconds, a binary operator the operand
// of another. The two children of every binary node differ, so a child moved,
// swapped or dropped changes the formula's wire.
#pragma once

#include <aletheia/ltl.hpp>
#include <aletheia/types.hpp>

#include <memory>
#include <utility>

namespace aletheia::test {

[[nodiscard]] inline auto every_alternative() -> LtlFormula {
    using namespace ltl;
    SignalName const speed{"Speed"};
    auto const eq = atomic(equals(speed, PhysicalValue{Rational{1, 1}}));
    auto const lt = atomic(less_than(speed, PhysicalValue{Rational{3, 2}}));
    auto const gt = atomic(greater_than(speed, PhysicalValue{Rational{7, 1}}));
    auto const le = atomic(less_than_or_equal(speed, PhysicalValue{Rational{220, 1}}));
    auto const ge = atomic(greater_than_or_equal(SignalName{"RPM"}, PhysicalValue{Rational{0, 1}}));
    auto const bt = atomic(between(SignalName{"Temp"}, PhysicalValue{Rational{-40, 1}},
                                   PhysicalValue{Rational{215, 1}}));
    auto const rise = atomic(changed_by(SignalName{"Pos"}, Delta{Rational{5, 2}}));
    auto const fall = atomic(changed_by(SignalName{"Neg"}, Delta{Rational{-5, 2}}));
    auto const steady = atomic(stable_within(SignalName{"Volt"}, Tolerance{Rational{1, 100}}));
    // always(not P) is the shape the printer writes as `never P`.
    auto never_eq = always(negate(clone(eq)));
    auto unary = both(next(clone(lt)), either(weak_next(clone(gt)), negate(clone(le))));
    auto temporal = until(always(clone(ge)), release(eventually(clone(bt)), clone(rise)));
    // Two seconds, then 1500 microseconds, which is no whole millisecond, then 7.
    auto metric_until = MetricUntil{.bound = Timestamp{2'000'000},
                                    .left = std::make_unique<LtlFormula>(clone(fall)),
                                    .right = std::make_unique<LtlFormula>(clone(steady))};
    auto metric_release =
        MetricRelease{.bound = Timestamp{1'500},
                      .left = std::make_unique<LtlFormula>(std::move(metric_until)),
                      .right = std::make_unique<LtlFormula>(within(Timestamp{7}, clone(eq)))};
    auto metric_always = always_within(Timestamp{250'000}, clone(lt));
    return both(both(std::move(never_eq), std::move(unary)),
                either(std::move(temporal),
                       both(LtlFormula{std::move(metric_release)}, std::move(metric_always))));
}

} // namespace aletheia::test
