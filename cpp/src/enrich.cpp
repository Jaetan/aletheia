// Enrichment logic: formula pretty-printer, signal collector, diagnostics.
#include <aletheia/enrich.hpp>

#include <algorithm>
#include <cstdint>
#include <format>
#include <string>
#include <vector>

namespace aletheia {
namespace {

auto format_value(double v) -> std::string {
    return std::format("{:g}", v);
}

auto format_timebound(Timestamp t) -> std::string {
    auto us = t.count();
    if (us % 1'000'000 == 0)
        return std::format("{}s ", us / 1'000'000);
    if (us % 1'000 == 0)
        return std::format("{}ms ", us / 1'000);
    return std::format("{}us ", us);
}

auto format_predicate(const Predicate& p) -> std::string {
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
                return std::format("|{}{}| > {}", "\xce\x94", std::string_view{v.signal},
                                   format_value(v.delta.get()));
            else
                static_assert(sizeof(T) == 0, "Unhandled predicate type in format_predicate");
        },
        p);
}

auto predicate_signal(const Predicate& p) -> SignalName {
    return std::visit([](const auto& v) -> SignalName { return v.signal; }, p);
}

void collect_signals_into(const LtlFormula& f, std::vector<SignalName>& signals) {
    std::visit(
        [&signals](const auto& v) {
            using T = std::decay_t<decltype(v)>;
            if constexpr (std::is_same_v<T, Atomic>) {
                auto name = predicate_signal(v.predicate);
                if (std::ranges::find(signals, name) == signals.end())
                    signals.push_back(name);
            } else if constexpr (std::is_same_v<T, Not>) {
                collect_signals_into(*v.formula, signals);
            } else if constexpr (std::is_same_v<T, And> || std::is_same_v<T, Or> ||
                                 std::is_same_v<T, Until> || std::is_same_v<T, Release>) {
                collect_signals_into(*v.left, signals);
                collect_signals_into(*v.right, signals);
            } else if constexpr (std::is_same_v<T, Next> || std::is_same_v<T, Always> ||
                                 std::is_same_v<T, Eventually>) {
                collect_signals_into(*v.formula, signals);
            } else if constexpr (std::is_same_v<T, MetricAlways> ||
                                 std::is_same_v<T, MetricEventually>) {
                collect_signals_into(*v.formula, signals);
            } else if constexpr (std::is_same_v<T, MetricUntil> ||
                                 std::is_same_v<T, MetricRelease>) {
                collect_signals_into(*v.left, signals);
                collect_signals_into(*v.right, signals);
            } else {
                static_assert(sizeof(T) == 0, "Unhandled formula type in collect_signals_into");
            }
        },
        f);
}

} // namespace

auto format_formula(const LtlFormula& f) -> std::string {
    return std::visit(
        [](const auto& v) -> std::string {
            using T = std::decay_t<decltype(v)>;
            if constexpr (std::is_same_v<T, Atomic>)
                return format_predicate(v.predicate);
            else if constexpr (std::is_same_v<T, Not>)
                return "not(" + format_formula(*v.formula) + ")";
            else if constexpr (std::is_same_v<T, And>)
                return format_formula(*v.left) + " and " + format_formula(*v.right);
            else if constexpr (std::is_same_v<T, Or>)
                return format_formula(*v.left) + " or " + format_formula(*v.right);
            else if constexpr (std::is_same_v<T, Next>)
                return "next(" + format_formula(*v.formula) + ")";
            else if constexpr (std::is_same_v<T, Always>) {
                // Detect Never pattern: Always{Not{Atomic{p}}}
                if (auto* n = std::get_if<Not>(v.formula.get()))
                    if (auto* a = std::get_if<Atomic>(n->formula.get()))
                        return "never " + format_predicate(a->predicate);
                return "always(" + format_formula(*v.formula) + ")";
            } else if constexpr (std::is_same_v<T, Eventually>)
                return "eventually(" + format_formula(*v.formula) + ")";
            else if constexpr (std::is_same_v<T, Until>)
                return format_formula(*v.left) + " until " + format_formula(*v.right);
            else if constexpr (std::is_same_v<T, Release>)
                return format_formula(*v.left) + " release " + format_formula(*v.right);
            else if constexpr (std::is_same_v<T, MetricAlways>)
                return "always within " + format_timebound(v.bound) + "(" +
                       format_formula(*v.formula) + ")";
            else if constexpr (std::is_same_v<T, MetricEventually>)
                return "eventually within " + format_timebound(v.bound) + "(" +
                       format_formula(*v.formula) + ")";
            else if constexpr (std::is_same_v<T, MetricUntil>)
                return format_formula(*v.left) + " until within " + format_timebound(v.bound) +
                       " " + format_formula(*v.right);
            else if constexpr (std::is_same_v<T, MetricRelease>)
                return format_formula(*v.left) + " release within " + format_timebound(v.bound) +
                       " " + format_formula(*v.right);
            else
                static_assert(sizeof(T) == 0, "Unhandled formula type in format_formula");
        },
        f);
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
