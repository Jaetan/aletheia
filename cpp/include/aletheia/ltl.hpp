// SPDX-FileCopyrightText: 2025 Nicolas Pelletier
// SPDX-License-Identifier: BSD-2-Clause
#pragma once

// ltl.hpp's predicate and formula structs embed SignalName/PhysicalValue/
// Delta/Tolerance/Timestamp from types.hpp, so callers that include ltl.hpp
// always need those vocabulary types.
#include <aletheia/types.hpp> // IWYU pragma: export

#include <concepts>
#include <memory>
#include <type_traits>
#include <utility>
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
// LTL formula: recursive variant via composition
// ---------------------------------------------------------------------------
//
// Composition rather than inheriting from std::variant: inheriting is
// permitted by the standard but hits libstdc++ implementation quirks across
// versions (special-member-function constraints, in_place_index_t deduction
// in derived ctors); composition costs one `.value` indirection.
//
// The alternative list is owned by `LtlFormulaVariant` (one source of
// truth); the wrapper provides a constrained converting constructor + a
// `visit` member so consumers don't reach into the variant by name.
//
// A "Visitor pattern for binary-compat extension" is intentionally not
// pursued here — LtlFormula is consumed header-only with std::visit lambdas
// everywhere, and the LTL ADT mirrors the Agda kernel's constructor set 1:1,
// so adding an alternative requires kernel changes that recompile every
// consumer regardless of dispatch style.  Virtual-dispatch Visitor would lose
// constexpr and break the lambda idiom for no architectural gain.

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
struct WeakNext {
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

using LtlFormulaVariant =
    std::variant<Atomic, Not, And, Or, Next, WeakNext, Always, Eventually, Until, Release,
                 MetricAlways, MetricEventually, MetricUntil, MetricRelease>;

struct LtlFormula {
    LtlFormulaVariant value;

    // Default constructor intentionally omitted — none of the alternative
    // structs is default-constructible (`Strong<Tag, T>` blocks default-init
    // by design), so the variant has no default state to initialize to.

    template<typename T>
        requires(!std::same_as<std::decay_t<T>, LtlFormula>) &&
                std::constructible_from<LtlFormulaVariant, T>
    // NOLINTNEXTLINE(google-explicit-constructor,misc-explicit-constructor,cppcoreguidelines-explicit-constructor)
    LtlFormula(T&& v) : value(std::forward<T>(v)) {}

    template<typename Visitor>
    constexpr auto visit(Visitor&& vis) const& -> decltype(auto) {
        return std::visit(std::forward<Visitor>(vis), value);
    }
    template<typename Visitor>
    constexpr auto visit(Visitor&& vis) & -> decltype(auto) {
        return std::visit(std::forward<Visitor>(vis), value);
    }
    template<typename Visitor>
    constexpr auto visit(Visitor&& vis) && -> decltype(auto) {
        return std::visit(std::forward<Visitor>(vis), std::move(value));
    }
};

// ---------------------------------------------------------------------------
// Builder functions (convenience, mirrors Python Check DSL)
// ---------------------------------------------------------------------------

namespace ltl {

// --- Formula constructors ---

[[nodiscard]] inline auto atomic(Predicate p) -> LtlFormula {
    return Atomic{std::move(p)};
}

[[nodiscard]] inline auto negate(LtlFormula f) -> LtlFormula {
    return Not{std::make_unique<LtlFormula>(std::move(f))};
}

[[nodiscard]] inline auto both(LtlFormula left, LtlFormula right) -> LtlFormula {
    return And{.left = std::make_unique<LtlFormula>(std::move(left)),
               .right = std::make_unique<LtlFormula>(std::move(right))};
}

[[nodiscard]] inline auto either(LtlFormula left, LtlFormula right) -> LtlFormula {
    return Or{.left = std::make_unique<LtlFormula>(std::move(left)),
              .right = std::make_unique<LtlFormula>(std::move(right))};
}

// antecedent -> consequent, the standard LTL encoding !antecedent || consequent.
// A convenience combinator (implication is not a distinct LtlFormula node);
// mirrors Go's Implies, Rust's Formula::implies, and Python's .implies().
[[nodiscard]] inline auto implies(LtlFormula antecedent, LtlFormula consequent) -> LtlFormula {
    return either(negate(std::move(antecedent)), std::move(consequent));
}

[[nodiscard]] inline auto next(LtlFormula f) -> LtlFormula {
    return Next{std::make_unique<LtlFormula>(std::move(f))};
}

[[nodiscard]] inline auto weak_next(LtlFormula f) -> LtlFormula {
    return WeakNext{std::make_unique<LtlFormula>(std::move(f))};
}

[[nodiscard]] inline auto always(LtlFormula f) -> LtlFormula {
    return Always{std::make_unique<LtlFormula>(std::move(f))};
}

[[nodiscard]] inline auto eventually(LtlFormula f) -> LtlFormula {
    return Eventually{std::make_unique<LtlFormula>(std::move(f))};
}

[[nodiscard]] inline auto never(Predicate p) -> LtlFormula {
    return always(negate(atomic(std::move(p))));
}

[[nodiscard]] inline auto until(LtlFormula left, LtlFormula right) -> LtlFormula {
    return Until{.left = std::make_unique<LtlFormula>(std::move(left)),
                 .right = std::make_unique<LtlFormula>(std::move(right))};
}

[[nodiscard]] inline auto release(LtlFormula left, LtlFormula right) -> LtlFormula {
    return Release{.left = std::make_unique<LtlFormula>(std::move(left)),
                   .right = std::make_unique<LtlFormula>(std::move(right))};
}

[[nodiscard]] inline auto within(Timestamp t, LtlFormula f) -> LtlFormula {
    return MetricEventually{.bound = t, .formula = std::make_unique<LtlFormula>(std::move(f))};
}

[[nodiscard]] inline auto always_within(Timestamp t, LtlFormula f) -> LtlFormula {
    return MetricAlways{.bound = t, .formula = std::make_unique<LtlFormula>(std::move(f))};
}

// --- Predicate builders ---

[[nodiscard]] inline auto equals(SignalName name, PhysicalValue value) -> Predicate {
    return Equals{.signal = std::move(name), .value = value};
}

[[nodiscard]] inline auto less_than(SignalName name, PhysicalValue value) -> Predicate {
    return LessThan{.signal = std::move(name), .value = value};
}

[[nodiscard]] inline auto greater_than(SignalName name, PhysicalValue value) -> Predicate {
    return GreaterThan{.signal = std::move(name), .value = value};
}

[[nodiscard]] inline auto less_than_or_equal(SignalName name, PhysicalValue value) -> Predicate {
    return LessThanOrEqual{.signal = std::move(name), .value = value};
}

[[nodiscard]] inline auto greater_than_or_equal(SignalName name, PhysicalValue value) -> Predicate {
    return GreaterThanOrEqual{.signal = std::move(name), .value = value};
}

[[nodiscard]] inline auto between(SignalName name, PhysicalValue min, PhysicalValue max)
    -> Predicate {
    return Between{.signal = std::move(name), .min = min, .max = max};
}

[[nodiscard]] inline auto changed_by(SignalName name, Delta delta) -> Predicate {
    return ChangedBy{.signal = std::move(name), .delta = delta};
}

[[nodiscard]] inline auto stable_within(SignalName name, Tolerance tol) -> Predicate {
    return StableWithin{.signal = std::move(name), .tolerance = tol};
}

// Deep-copy a formula tree (LtlFormula contains unique_ptr children). Every
// alternative is one of five aggregate shapes, which the branches below name
// by their members rather than by type; an alternative of a new shape fails
// the final static_assert.
[[nodiscard]] inline auto clone(const LtlFormula& f) -> LtlFormula {
    auto cp = [](const std::unique_ptr<LtlFormula>& p) -> std::unique_ptr<LtlFormula> {
        return p ? std::make_unique<LtlFormula>(clone(*p)) : nullptr;
    };
    return f.visit([&cp](auto const& v) -> LtlFormula {
        using T = std::decay_t<decltype(v)>;
        if constexpr (requires { v.predicate; })
            return T{v.predicate};
        else if constexpr (requires {
                               v.bound;
                               v.left;
                               v.right;
                           })
            return T{v.bound, cp(v.left), cp(v.right)};
        else if constexpr (requires {
                               v.bound;
                               v.formula;
                           })
            return T{v.bound, cp(v.formula)};
        else if constexpr (requires {
                               v.left;
                               v.right;
                           })
            return T{cp(v.left), cp(v.right)};
        else if constexpr (requires { v.formula; })
            return T{cp(v.formula)};
        else
            static_assert(sizeof(T) == 0, "Unhandled formula shape in clone");
    });
}

} // namespace ltl
} // namespace aletheia
