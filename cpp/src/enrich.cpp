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

static auto format_value(double v) -> std::string {
    return std::format("{:g}", v);
}

// Cross-binding-identical Rational pretty-printer.  Every render flows
// through the Agda kernel via `aletheia_format_rational` (R20 cluster
// Y stage 2): the C++ binding calls the same function as Python and
// Go, so the same Rational value renders to byte-identical output
// everywhere.  The library is dlopened on first use via the lazy-load
// in `rational_renderer.cpp`; no local C++ fallback exists.  A missing
// `libaletheia-ffi.so` throws `AletheiaException(Ffi)` rather than
// silently diverging.
static auto format_value(const Rational& r) -> std::string {
    return detail::format_rational_ffi(r.numerator(), r.denominator());
}

constexpr std::int64_t us_per_second = 1'000'000;
constexpr std::int64_t us_per_millisecond = 1'000;

static auto format_timebound(Timestamp t) -> std::string {
    auto us = t.count();
    if (us % us_per_second == 0)
        return std::format("{}s ", us / us_per_second);
    if (us % us_per_millisecond == 0)
        return std::format("{}ms ", us / us_per_millisecond);
    return std::format("{}\u03bcs ", us);
}

static auto format_predicate(const Predicate& p) -> std::string {
    return std::visit(
        [](const auto& v) -> std::string {
            using T = std::decay_t<decltype(v)>;
            if constexpr (std::is_same_v<T, Equals>)
                return std::format("{} = {}", std::string_view{v.signal},
                                   format_value(v.value.get()));
            else if constexpr (std::is_same_v<T, LessThan>)
                return std::format("{} < {}", std::string_view{v.signal},
                                   format_value(v.value.get()));
            else if constexpr (std::is_same_v<T, GreaterThan>)
                return std::format("{} > {}", std::string_view{v.signal},
                                   format_value(v.value.get()));
            else if constexpr (std::is_same_v<T, LessThanOrEqual>)
                return std::format("{} <= {}", std::string_view{v.signal},
                                   format_value(v.value.get()));
            else if constexpr (std::is_same_v<T, GreaterThanOrEqual>)
                return std::format("{} >= {}", std::string_view{v.signal},
                                   format_value(v.value.get()));
            else if constexpr (std::is_same_v<T, Between>)
                return std::format("{} <= {} <= {}", format_value(v.min.get()),
                                   std::string_view{v.signal}, format_value(v.max.get()));
            else if constexpr (std::is_same_v<T, ChangedBy>)
                // U+0394 Greek Capital Letter Delta (UTF-8: CE 94)
                // R19 cluster 7 — CPP-D-19.2: Delta is now Rational; compare
                // against Rational{0, 1} via the Rational `<=>` operator.
                return v.delta.get() >= Rational{0, 1}
                           ? std::format("{}{} >= {}", "\xce\x94", std::string_view{v.signal},
                                         format_value(v.delta.get()))
                           : std::format("{}{} <= {}", "\xce\x94", std::string_view{v.signal},
                                         format_value(v.delta.get()));
            else if constexpr (std::is_same_v<T, StableWithin>)
                return std::format("|{}{}| <= {}", "\xce\x94", std::string_view{v.signal},
                                   format_value(v.tolerance.get()));
            else
                static_assert(sizeof(T) == 0, "Unhandled predicate type in format_predicate");
        },
        p);
}

static auto predicate_signal(const Predicate& p) -> SignalName {
    return std::visit([](const auto& v) -> SignalName { return v.signal; }, p);
}

static void collect_signals_into(const LtlFormula& f, std::vector<SignalName>& signals) {
    f.visit([&signals](const auto& v) {
        using T = std::decay_t<decltype(v)>;
        if constexpr (std::is_same_v<T, Atomic>) {
            auto name = predicate_signal(v.predicate);
            if (std::ranges::find(signals, name) == signals.end())
                signals.push_back(name);
        } else if constexpr (std::is_same_v<T, Not> || std::is_same_v<T, Next> ||
                             std::is_same_v<T, WeakNext> || std::is_same_v<T, Always> ||
                             std::is_same_v<T, Eventually> || std::is_same_v<T, MetricAlways> ||
                             std::is_same_v<T, MetricEventually>) {
            collect_signals_into(*v.formula, signals);
        } else if constexpr (std::is_same_v<T, And> || std::is_same_v<T, Or> ||
                             std::is_same_v<T, Until> || std::is_same_v<T, Release> ||
                             std::is_same_v<T, MetricUntil> || std::is_same_v<T, MetricRelease>) {
            collect_signals_into(*v.left, signals);
            collect_signals_into(*v.right, signals);
        } else {
            static_assert(sizeof(T) == 0, "Unhandled formula type in collect_signals_into");
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
static auto format_metric_binary(const Node& v, std::string_view op, bool parenthesize) -> std::string {
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
// they appear as children of other binary operators, matching Go's behavior.
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
