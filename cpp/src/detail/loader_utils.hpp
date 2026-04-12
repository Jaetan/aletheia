// SPDX-License-Identifier: BSD-2-Clause
//
// Shared condition dispatch logic for YAML and Excel check loaders.
//
// Both loaders accept the same set of condition keywords and dispatch them
// through the same Check API builders.  This header defines the keyword
// constants and dispatch helpers so the two loaders stay in sync.
//
#pragma once

#include <aletheia/check.hpp>
#include <aletheia/types.hpp>

#include <cmath>
#include <cstdint>
#include <numeric>
#include <string>

namespace aletheia::detail {

// ---------------------------------------------------------------------------
// Condition dispatch helpers
// ---------------------------------------------------------------------------

/// Apply a simple single-signal, single-value condition (never_exceeds/below/equals).
inline auto dispatch_simple(const std::string& signal, const std::string& condition,
                            PhysicalValue value) -> CheckResult {
    if (condition == "never_exceeds")
        return Check::signal(signal).never_exceeds(value);
    if (condition == "never_below")
        return Check::signal(signal).never_below(value);
    if (condition == "never_equals")
        return Check::signal(signal).never_equals(value);
    // Caller must validate condition before calling; unreachable in correct usage.
    throw std::invalid_argument("Unknown simple condition: " + condition);
}

/// Apply a when-condition to a WhenSignal builder.
inline auto dispatch_when(WhenSignal& builder, const std::string& condition, PhysicalValue value)
    -> WhenCondition {
    if (condition == "exceeds")
        return builder.exceeds(value);
    if (condition == "equals")
        return builder.equals(value);
    if (condition == "drops_below")
        return builder.drops_below(value);
    throw std::invalid_argument("Unknown when condition: " + condition);
}

// ---------------------------------------------------------------------------
// Condition keyword predicates
// ---------------------------------------------------------------------------

inline auto is_simple_value_condition(const std::string& c) -> bool {
    return c == "never_exceeds" || c == "never_below" || c == "never_equals";
}

inline auto is_simple_range_condition(const std::string& c) -> bool {
    return c == "stays_between";
}

inline auto is_simple_settles_condition(const std::string& c) -> bool {
    return c == "settles_between";
}

inline auto is_simple_condition(const std::string& c) -> bool {
    return is_simple_value_condition(c) || is_simple_range_condition(c) ||
           is_simple_settles_condition(c) || c == "equals";
}

inline auto is_when_condition(const std::string& c) -> bool {
    return c == "exceeds" || c == "equals" || c == "drops_below";
}

inline auto is_then_condition(const std::string& c) -> bool {
    return c == "equals" || c == "exceeds" || c == "stays_between";
}

// ---------------------------------------------------------------------------
// double -> Rational conversion (for Excel-sourced numeric values)
// ---------------------------------------------------------------------------

/// Convert a double to an exact Rational.
///
/// If the value is an exact integer, returns {int_val, 1}.
/// Otherwise, uses fixed 6-decimal precision with GCD simplification.
inline auto double_to_rational(double value) -> Rational {
    if (value == std::floor(value) && std::abs(value) < 1e15)
        return {.numerator = static_cast<std::int64_t>(value), .denominator = 1};
    constexpr std::int64_t scale = 1'000'000;
    auto num = static_cast<std::int64_t>(std::round(value * scale));
    auto divisor = std::gcd(std::abs(num), scale);
    return {.numerator = num / divisor, .denominator = scale / divisor};
}

} // namespace aletheia::detail
