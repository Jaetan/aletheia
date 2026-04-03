// SPDX-License-Identifier: BSD-2-Clause
#pragma once

#include <aletheia/types.hpp>

#include <memory>
#include <variant>

namespace aletheia {

// ---------------------------------------------------------------------------
// Predicates: what to check about a signal
// ---------------------------------------------------------------------------

struct Equals {
    SignalName signal;
    PhysicalValue value;
};
struct LessThan {
    SignalName signal;
    PhysicalValue value;
};
struct GreaterThan {
    SignalName signal;
    PhysicalValue value;
};
struct LessThanOrEqual {
    SignalName signal;
    PhysicalValue value;
};
struct GreaterThanOrEqual {
    SignalName signal;
    PhysicalValue value;
};
struct Between {
    SignalName signal;
    PhysicalValue min;
    PhysicalValue max;
};
struct ChangedBy {
    SignalName signal;
    Delta delta;
};
struct StableWithin {
    SignalName signal;
    Tolerance tolerance;
};

using Predicate = std::variant<Equals, LessThan, GreaterThan, LessThanOrEqual, GreaterThanOrEqual,
                               Between, ChangedBy, StableWithin>;

// ---------------------------------------------------------------------------
// LTL formula: recursive variant via inheritance
// ---------------------------------------------------------------------------

struct LtlFormula;

struct Atomic {
    Predicate predicate;
};
struct Not {
    std::unique_ptr<LtlFormula> formula;
};
struct And {
    std::unique_ptr<LtlFormula> left, right;
};
struct Or {
    std::unique_ptr<LtlFormula> left, right;
};
struct Next {
    std::unique_ptr<LtlFormula> formula;
};
struct Always {
    std::unique_ptr<LtlFormula> formula;
};
struct Eventually {
    std::unique_ptr<LtlFormula> formula;
};
struct Until {
    std::unique_ptr<LtlFormula> left, right;
};
struct Release {
    std::unique_ptr<LtlFormula> left, right;
};
struct MetricAlways {
    Timestamp bound;
    std::unique_ptr<LtlFormula> formula;
};
struct MetricEventually {
    Timestamp bound;
    std::unique_ptr<LtlFormula> formula;
};
struct MetricUntil {
    Timestamp bound;
    std::unique_ptr<LtlFormula> left, right;
};
struct MetricRelease {
    Timestamp bound;
    std::unique_ptr<LtlFormula> left, right;
};

struct LtlFormula : std::variant<Atomic, Not, And, Or, Next, Always, Eventually, Until, Release,
                                 MetricAlways, MetricEventually, MetricUntil, MetricRelease> {
    using variant::variant;
};

// ---------------------------------------------------------------------------
// Builder functions (convenience, mirrors Python Check DSL)
// ---------------------------------------------------------------------------

namespace ltl {

// --- Formula constructors ---

inline auto atomic(Predicate p) -> LtlFormula {
    return Atomic{std::move(p)};
}

inline auto negate(LtlFormula f) -> LtlFormula {
    return Not{std::make_unique<LtlFormula>(std::move(f))};
}

inline auto both(LtlFormula left, LtlFormula right) -> LtlFormula {
    return And{.left = std::make_unique<LtlFormula>(std::move(left)),
               .right = std::make_unique<LtlFormula>(std::move(right))};
}

inline auto either(LtlFormula left, LtlFormula right) -> LtlFormula {
    return Or{.left = std::make_unique<LtlFormula>(std::move(left)),
              .right = std::make_unique<LtlFormula>(std::move(right))};
}

inline auto next(LtlFormula f) -> LtlFormula {
    return Next{std::make_unique<LtlFormula>(std::move(f))};
}

inline auto always(LtlFormula f) -> LtlFormula {
    return Always{std::make_unique<LtlFormula>(std::move(f))};
}

inline auto eventually(LtlFormula f) -> LtlFormula {
    return Eventually{std::make_unique<LtlFormula>(std::move(f))};
}

inline auto never(Predicate p) -> LtlFormula {
    return always(negate(atomic(std::move(p))));
}

inline auto until(LtlFormula left, LtlFormula right) -> LtlFormula {
    return Until{.left = std::make_unique<LtlFormula>(std::move(left)),
                 .right = std::make_unique<LtlFormula>(std::move(right))};
}

inline auto release(LtlFormula left, LtlFormula right) -> LtlFormula {
    return Release{.left = std::make_unique<LtlFormula>(std::move(left)),
                   .right = std::make_unique<LtlFormula>(std::move(right))};
}

inline auto within(Timestamp t, LtlFormula f) -> LtlFormula {
    return MetricEventually{.bound = t, .formula = std::make_unique<LtlFormula>(std::move(f))};
}

inline auto always_within(Timestamp t, LtlFormula f) -> LtlFormula {
    return MetricAlways{.bound = t, .formula = std::make_unique<LtlFormula>(std::move(f))};
}

// --- Predicate builders ---

inline auto equals(SignalName name, PhysicalValue value) -> Predicate {
    return Equals{.signal = std::move(name), .value = value};
}

inline auto less_than(SignalName name, PhysicalValue value) -> Predicate {
    return LessThan{.signal = std::move(name), .value = value};
}

inline auto greater_than(SignalName name, PhysicalValue value) -> Predicate {
    return GreaterThan{.signal = std::move(name), .value = value};
}

inline auto at_most(SignalName name, PhysicalValue value) -> Predicate {
    return LessThanOrEqual{.signal = std::move(name), .value = value};
}

inline auto at_least(SignalName name, PhysicalValue value) -> Predicate {
    return GreaterThanOrEqual{.signal = std::move(name), .value = value};
}

inline auto between(SignalName name, PhysicalValue min, PhysicalValue max) -> Predicate {
    return Between{.signal = std::move(name), .min = min, .max = max};
}

inline auto changed_by(SignalName name, Delta delta) -> Predicate {
    return ChangedBy{.signal = std::move(name), .delta = delta};
}

inline auto stable_within(SignalName name, Tolerance tol) -> Predicate {
    return StableWithin{.signal = std::move(name), .tolerance = tol};
}

} // namespace ltl
} // namespace aletheia
