// SPDX-FileCopyrightText: 2025 Nicolas Pelletier
// SPDX-License-Identifier: BSD-2-Clause
// Enrichment logic: formula pretty-printer, signal collector, diagnostics, and
// the check builder's description renderer.
#include <aletheia/enrich.hpp>

#include <aletheia/check.hpp>
#include <aletheia/detail/checked.hpp>
#include <aletheia/detail/rational_renderer.hpp>
#include <aletheia/error.hpp>

#include <algorithm>
#include <expected>
#include <format>
#include <optional>
#include <span>
#include <string>
#include <string_view>
#include <type_traits>
#include <utility>
#include <variant>
#include <vector>

namespace aletheia {

auto detail::render_desc(std::span<DescPart const> parts) -> Result<std::string> {
    std::string out;
    for (auto const& part : parts) {
        if (auto const* text = std::get_if<std::string>(&part)) {
            out += *text;
            continue;
        }
        auto const rendered = format_rational(std::get<Rational>(part));
        if (!rendered)
            return std::unexpected(detail::error_of(rendered));
        out += rendered.value();
    }
    return out;
}

// A bound as an inverted range's refusal prints it: the kernel's rendering, or
// `n` or `n/d` while the runtime is down, since a check is built before any
// start too.
static auto bound_text(Rational const& r) -> std::string {
    auto rendered = detail::format_rational(r);
    if (rendered)
        return std::move(rendered).value();
    if (r.denominator() == 1)
        return std::to_string(r.numerator());
    return std::format("{}/{}", r.numerator(), r.denominator());
}

auto detail::range_refusal(std::string_view op, PhysicalValue lo, PhysicalValue hi)
    -> std::optional<std::string> {
    if (lo.get() <= hi.get())
        return std::nullopt;
    return std::format("{}: lo ({}) must be <= hi ({})", op, bound_text(lo.get()),
                       bound_text(hi.get()));
}

// Greek capital delta, the change-predicate prefix.
constexpr std::string_view k_delta = "\u0394";

static auto format_timebound(Timestamp t) -> std::string {
    auto const us = t.count();
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
static auto format_predicate(Predicate const& p) -> Result<std::string> {
    return std::visit(
        [](auto const& v) -> Result<std::string> {
            using T = std::decay_t<decltype(v)>;
            auto const signal = std::string_view{v.signal};
            if constexpr (requires { v.value; })
                return detail::format_rational(v.value.get()).transform([&](auto const& value) {
                    return std::format("{} {} {}", signal, comparison_token<T>(), value);
                });
            else if constexpr (requires {
                                   v.min;
                                   v.max;
                               })
                return detail::format_rational(v.min.get()).and_then([&](auto const& lo) {
                    return detail::format_rational(v.max.get()).transform([&](auto const& hi) {
                        return std::format("{} <= {} <= {}", lo, signal, hi);
                    });
                });
            else if constexpr (requires { v.delta; })
                // The sign of the delta says which direction the change bounds.
                return detail::format_rational(v.delta.get()).transform([&](auto const& delta) {
                    return std::format("{}{} {} {}", k_delta, signal,
                                       v.delta.get() >= Rational{0, 1} ? ">=" : "<=", delta);
                });
            else if constexpr (requires { v.tolerance; })
                return detail::format_rational(v.tolerance.get()).transform([&](auto const& tol) {
                    return std::format("|{}{}| <= {}", k_delta, signal, tol);
                });
            else
                static_assert(sizeof(T) == 0, "Unhandled predicate shape in format_predicate");
        },
        p);
}

static auto predicate_signal(Predicate const& p) -> SignalName {
    return std::visit([](auto const& v) -> SignalName { return v.signal; }, p);
}

// Walks the tree by shape (a predicate, two children, or one), so an
// alternative of an existing shape needs no branch here.
static void collect_signals_into(LtlFormula const& f, std::vector<SignalName>& signals) {
    f.visit([&signals](auto const& v) {
        using T = std::decay_t<decltype(v)>;
        if constexpr (requires { v.predicate; }) {
            auto const name = predicate_signal(v.predicate);
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

static auto format_formula_inner(LtlFormula const& f, bool parenthesize_binary)
    -> Result<std::string>;

static auto wrap_if_binary(std::string s, bool parenthesize) -> std::string {
    return parenthesize ? "(" + std::move(s) + ")" : std::move(s);
}

// `<left> <infix><right>`, each child parenthesized when binary.
template<typename Node>
static auto format_infix(Node const& v, std::string infix, bool parenthesize)
    -> Result<std::string> {
    return format_formula_inner(*v.left, true).and_then([&](auto const& left) {
        return format_formula_inner(*v.right, true).transform([&](auto const& right) {
            return wrap_if_binary(left + " " + infix + right, parenthesize);
        });
    });
}

template<typename Node>
static auto format_binary(Node const& v, std::string_view op, bool parenthesize)
    -> Result<std::string> {
    return format_infix(v, std::string{op} + " ", parenthesize);
}

template<typename Node>
static auto format_metric_binary(Node const& v, std::string_view op, bool parenthesize)
    -> Result<std::string> {
    return format_infix(v, std::string{op} + " within " + format_timebound(v.bound), parenthesize);
}

// `<prefix>(<child>)`, the child never parenthesized again.
static auto format_unary(std::string_view prefix, LtlFormula const& child) -> Result<std::string> {
    return format_formula_inner(child, false).transform([prefix](auto const& inner) {
        return std::string{prefix} + "(" + inner + ")";
    });
}

// The Never pattern Always{Not{Atomic{p}}} as `never <p>`, or nullopt for any
// other Always.
static auto try_format_never(Always const& v) -> std::optional<Result<std::string>> {
    if (auto* n = std::get_if<Not>(&v.formula->value))
        if (auto const* a = std::get_if<Atomic>(&n->formula->value))
            return format_predicate(a->predicate).transform([](auto const& predicate) {
                return "never " + predicate;
            });
    return std::nullopt;
}

// Inner formatter: parenthesize_binary wraps binary operators in parens when
// they appear as children of other binary operators.  The whole rendering is
// byte-identical to the Python and Go formatters; a probe under probes/
// compares this formatter against Python's over every alternative.
static auto format_formula_inner(LtlFormula const& f, bool parenthesize_binary)
    -> Result<std::string> {
    return f.visit([parenthesize_binary](auto const& v) -> Result<std::string> {
        using T = std::decay_t<decltype(v)>;
        if constexpr (std::is_same_v<T, Atomic>) {
            return format_predicate(v.predicate);
        } else if constexpr (std::is_same_v<T, Not>) {
            return format_unary("not", *v.formula);
        } else if constexpr (std::is_same_v<T, And>) {
            return format_binary(v, "and", parenthesize_binary);
        } else if constexpr (std::is_same_v<T, Or>) {
            return format_binary(v, "or", parenthesize_binary);
        } else if constexpr (std::is_same_v<T, Next>) {
            return format_unary("next", *v.formula);
        } else if constexpr (std::is_same_v<T, WeakNext>) {
            return format_unary("weak_next", *v.formula);
        } else if constexpr (std::is_same_v<T, Always>) {
            if (auto never = try_format_never(v))
                return std::move(never).value();
            return format_unary("always", *v.formula);
        } else if constexpr (std::is_same_v<T, Eventually>) {
            return format_unary("eventually", *v.formula);
        } else if constexpr (std::is_same_v<T, Until>) {
            return format_binary(v, "until", parenthesize_binary);
        } else if constexpr (std::is_same_v<T, Release>) {
            return format_binary(v, "release", parenthesize_binary);
        } else if constexpr (std::is_same_v<T, MetricAlways>) {
            return format_unary("always within " + format_timebound(v.bound), *v.formula);
        } else if constexpr (std::is_same_v<T, MetricEventually>) {
            return format_unary("eventually within " + format_timebound(v.bound), *v.formula);
        } else if constexpr (std::is_same_v<T, MetricUntil>) {
            return format_metric_binary(v, "until", parenthesize_binary);
        } else if constexpr (std::is_same_v<T, MetricRelease>) {
            return format_metric_binary(v, "release", parenthesize_binary);
        } else {
            static_assert(sizeof(T) == 0, "Unhandled formula type in format_formula");
        }
    });
}

auto format_formula(LtlFormula const& f) -> Result<std::string> {
    return format_formula_inner(f, false);
}

auto collect_signals(LtlFormula const& f) -> std::vector<SignalName> {
    std::vector<SignalName> signals;
    collect_signals_into(f, signals);
    return signals;
}

auto build_diagnostic(LtlFormula const& f) -> Result<PropertyDiagnostic> {
    return format_formula(f).transform([&f](std::string desc) {
        return PropertyDiagnostic{
            .signals = collect_signals(f),
            .formula_desc = std::move(desc),
        };
    });
}

} // namespace aletheia
