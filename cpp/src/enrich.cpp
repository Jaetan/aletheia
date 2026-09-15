// SPDX-FileCopyrightText: 2025 Nicolas Pelletier
// SPDX-License-Identifier: BSD-2-Clause
// Enrichment logic: formula pretty-printer, signal collector, diagnostics.
#include <aletheia/enrich.hpp>

#include <aletheia/detail/rational_renderer.hpp>

#include <algorithm>
#include <cstdint>
#include <format>
#include <string>
#include <string_view>
#include <type_traits>
#include <utility>
#include <variant>
#include <vector>

namespace aletheia {

// Greek capital delta, the change-predicate prefix.
constexpr std::string_view k_delta = "\u0394";

static auto format_timebound(Timestamp t) -> std::string {
    auto us = t.count();
    if (us % us_per_second == 0)
        return std::format("{}s ", us / us_per_second);
    if (us % us_per_millisecond == 0)
        return std::format("{}ms ", us / us_per_millisecond);
    return std::format("{}\u03bcs ", us);
}

// The token a value-comparison predicate renders between its signal and its
// threshold.  The five such predicates differ in nothing else.
template<typename T>
static constexpr auto comparison_token() -> std::string_view {
    if constexpr (std::is_same_v<T, Equals>)
        return "=";
    else if constexpr (std::is_same_v<T, LessThan>)
        return "<";
    else if constexpr (std::is_same_v<T, GreaterThan>)
        return ">";
    else if constexpr (std::is_same_v<T, LessThanOrEqual>)
        return "<=";
    else if constexpr (std::is_same_v<T, GreaterThanOrEqual>)
        return ">=";
    else
        static_assert(sizeof(T) == 0, "not a value-comparison predicate");
}

// Every predicate is one of four shapes, named below by its members rather
// than by its type; a predicate of a new shape fails the final static_assert.
static auto format_predicate(const Predicate& p) -> std::string {
    return std::visit(
        [](const auto& v) -> std::string {
            using T = std::decay_t<decltype(v)>;
            if constexpr (requires { v.value; })
                return std::format("{} {} {}", std::string_view{v.signal}, comparison_token<T>(),
                                   detail::format_rational(v.value.get()));
            else if constexpr (requires {
                                   v.min;
                                   v.max;
                               })
                return std::format("{} <= {} <= {}", detail::format_rational(v.min.get()),
                                   std::string_view{v.signal},
                                   detail::format_rational(v.max.get()));
            else if constexpr (requires { v.delta; })
                // The sign of the delta says which direction the change bounds.
                return std::format("{}{} {} {}", k_delta, std::string_view{v.signal},
                                   v.delta.get() >= Rational{0, 1} ? ">=" : "<=",
                                   detail::format_rational(v.delta.get()));
            else if constexpr (requires { v.tolerance; })
                return std::format("|{}{}| <= {}", k_delta, std::string_view{v.signal},
                                   detail::format_rational(v.tolerance.get()));
            else
                static_assert(sizeof(T) == 0, "Unhandled predicate shape in format_predicate");
        },
        p);
}

static auto predicate_signal(const Predicate& p) -> SignalName {
    return std::visit([](const auto& v) -> SignalName { return v.signal; }, p);
}

// Walks the tree by shape (a predicate, two children, or one), so an
// alternative of an existing shape needs no branch here.
static void collect_signals_into(const LtlFormula& f, std::vector<SignalName>& signals) {
    f.visit([&signals](const auto& v) {
        using T = std::decay_t<decltype(v)>;
        if constexpr (requires { v.predicate; }) {
            auto name = predicate_signal(v.predicate);
            if (!std::ranges::contains(signals, name))
                signals.push_back(name);
        } else if constexpr (requires {
                                 v.left;
                                 v.right;
                             }) {
            collect_signals_into(*v.left, signals);
            collect_signals_into(*v.right, signals);
        } else if constexpr (requires { v.formula; }) {
            collect_signals_into(*v.formula, signals);
        } else {
            static_assert(sizeof(T) == 0, "Unhandled formula shape in collect_signals_into");
        }
    });
}

static auto format_formula_inner(const LtlFormula& f, bool parenthesize_binary) -> std::string;

static auto wrap_if_binary(std::string s, bool parenthesize) -> std::string {
    return parenthesize ? "(" + std::move(s) + ")" : std::move(s);
}

template<typename Node>
static auto format_binary(const Node& v, std::string_view op, bool parenthesize) -> std::string {
    return wrap_if_binary(format_formula_inner(*v.left, true) + " " + std::string{op} + " " +
                              format_formula_inner(*v.right, true),
                          parenthesize);
}

template<typename Node>
static auto format_metric_binary(const Node& v, std::string_view op, bool parenthesize)
    -> std::string {
    return wrap_if_binary(format_formula_inner(*v.left, true) + " " + std::string{op} + " within " +
                              format_timebound(v.bound) + format_formula_inner(*v.right, true),
                          parenthesize);
}

// Detect Never pattern: Always{Not{Atomic{p}}} — returns empty string if not.
static auto try_format_never(const Always& v) -> std::string {
    if (auto* n = std::get_if<Not>(&v.formula->value))
        if (auto* a = std::get_if<Atomic>(&n->formula->value))
            return "never " + format_predicate(a->predicate);
    return {};
}

// Inner formatter: parenthesize_binary wraps binary operators in parens when
// they appear as children of other binary operators.  The whole rendering is
// byte-identical to the Python and Go formatters; a probe under probes/
// compares this formatter against Python's over every alternative.
static auto format_formula_inner(const LtlFormula& f, bool parenthesize_binary) -> std::string {
    return f.visit([parenthesize_binary](const auto& v) -> std::string {
        using T = std::decay_t<decltype(v)>;
        if constexpr (std::is_same_v<T, Atomic>) {
            return format_predicate(v.predicate);
        } else if constexpr (std::is_same_v<T, Not>) {
            return "not(" + format_formula_inner(*v.formula, false) + ")";
        } else if constexpr (std::is_same_v<T, And>) {
            return format_binary(v, "and", parenthesize_binary);
        } else if constexpr (std::is_same_v<T, Or>) {
            return format_binary(v, "or", parenthesize_binary);
        } else if constexpr (std::is_same_v<T, Next>) {
            return "next(" + format_formula_inner(*v.formula, false) + ")";
        } else if constexpr (std::is_same_v<T, WeakNext>) {
            return "weak_next(" + format_formula_inner(*v.formula, false) + ")";
        } else if constexpr (std::is_same_v<T, Always>) {
            auto never = try_format_never(v);
            return never.empty() ? "always(" + format_formula_inner(*v.formula, false) + ")"
                                 : never;
        } else if constexpr (std::is_same_v<T, Eventually>) {
            return "eventually(" + format_formula_inner(*v.formula, false) + ")";
        } else if constexpr (std::is_same_v<T, Until>) {
            return format_binary(v, "until", parenthesize_binary);
        } else if constexpr (std::is_same_v<T, Release>) {
            return format_binary(v, "release", parenthesize_binary);
        } else if constexpr (std::is_same_v<T, MetricAlways>) {
            return "always within " + format_timebound(v.bound) + "(" +
                   format_formula_inner(*v.formula, false) + ")";
        } else if constexpr (std::is_same_v<T, MetricEventually>) {
            return "eventually within " + format_timebound(v.bound) + "(" +
                   format_formula_inner(*v.formula, false) + ")";
        } else if constexpr (std::is_same_v<T, MetricUntil>) {
            return format_metric_binary(v, "until", parenthesize_binary);
        } else if constexpr (std::is_same_v<T, MetricRelease>) {
            return format_metric_binary(v, "release", parenthesize_binary);
        } else {
            static_assert(sizeof(T) == 0, "Unhandled formula type in format_formula");
        }
    });
}

auto format_formula(const LtlFormula& f) -> std::string {
    return format_formula_inner(f, false);
}

auto collect_signals(const LtlFormula& f) -> std::vector<SignalName> {
    std::vector<SignalName> signals;
    collect_signals_into(f, signals);
    return signals;
}

auto build_diagnostic(const LtlFormula& f) -> PropertyDiagnostic {
    return PropertyDiagnostic{
        .signals = collect_signals(f),
        .formula_desc = format_formula(f),
    };
}

} // namespace aletheia
