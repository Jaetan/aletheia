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
// LTL formula: recursive variant via composition (R20 CPP-D-15.4 / 17.3)
// ---------------------------------------------------------------------------
//
// Previously inherited from std::variant via `using variant::variant`.
// Inheriting from std::variant is permitted by the standard but has hit
// libstdc++ implementation quirks across versions (special-member-function
// constraints, in_place_index_t deduction in derived ctors) — composition
// removes the hazard at the cost of one `.value` indirection.
//
// The 14-alternative list is owned by `LtlFormulaVariant` (one source of
// truth); the wrapper provides a constrained converting constructor + a
// `visit` member so consumers don't reach into the variant by name.
//
// Note on CPP-D-17.3: the reviewer's "Visitor pattern for binary-compat
// extension" framing is intentionally not pursued — LtlFormula is consumed
// header-only with std::visit lambdas everywhere, and the LTL ADT mirrors
// the Agda kernel's constructor set 1:1, so adding an alternative requires
// kernel changes that recompile every consumer regardless of dispatch style.
// Virtual-dispatch Visitor would lose constexpr and break the lambda
// idiom for no architectural gain.

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
    // Match the pre-refactor `using variant::variant` behaviour, which also
    // exposed no working default constructor.

    template<typename T>
        requires(!std::same_as<std::decay_t<T>, LtlFormula>) &&
                std::constructible_from<LtlFormulaVariant, T>
    LtlFormula(T&& v) // NOLINT(google-explicit-constructor,hicpp-explicit-conversions)
        : value(std::forward<T>(v)) {}

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

inline auto weak_next(LtlFormula f) -> LtlFormula {
    return WeakNext{std::make_unique<LtlFormula>(std::move(f))};
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

// Deep-copy a formula tree (LtlFormula contains unique_ptr children).
inline auto clone(const LtlFormula& f) -> LtlFormula {
    auto cp = [](const std::unique_ptr<LtlFormula>& p) -> std::unique_ptr<LtlFormula> {
        return p ? std::make_unique<LtlFormula>(clone(*p)) : nullptr;
    };
    return f.visit([&cp](const auto& v) -> LtlFormula {
        using T = std::decay_t<decltype(v)>;
        if constexpr (std::is_same_v<T, Atomic>)
            return Atomic{v.predicate};
        else if constexpr (std::is_same_v<T, Not>)
            return Not{cp(v.formula)};
        else if constexpr (std::is_same_v<T, And>)
            return And{cp(v.left), cp(v.right)};
        else if constexpr (std::is_same_v<T, Or>)
            return Or{cp(v.left), cp(v.right)};
        else if constexpr (std::is_same_v<T, Next>)
            return Next{cp(v.formula)};
        else if constexpr (std::is_same_v<T, WeakNext>)
            return WeakNext{cp(v.formula)};
        else if constexpr (std::is_same_v<T, Always>)
            return Always{cp(v.formula)};
        else if constexpr (std::is_same_v<T, Eventually>)
            return Eventually{cp(v.formula)};
        else if constexpr (std::is_same_v<T, Until>)
            return Until{cp(v.left), cp(v.right)};
        else if constexpr (std::is_same_v<T, Release>)
            return Release{cp(v.left), cp(v.right)};
        else if constexpr (std::is_same_v<T, MetricAlways>)
            return MetricAlways{v.bound, cp(v.formula)};
        else if constexpr (std::is_same_v<T, MetricEventually>)
            return MetricEventually{v.bound, cp(v.formula)};
        else if constexpr (std::is_same_v<T, MetricUntil>)
            return MetricUntil{v.bound, cp(v.left), cp(v.right)};
        else if constexpr (std::is_same_v<T, MetricRelease>)
            return MetricRelease{v.bound, cp(v.left), cp(v.right)};
        else
            static_assert(sizeof(T) == 0, "Unhandled formula type in clone");
    });
}

} // namespace ltl
} // namespace aletheia
