// SPDX-License-Identifier: BSD-2-Clause
// Rational::from_double — converts a double to an exact Rational.
#include <aletheia/types.hpp>

#include <cmath>
#include <cstdint>
#include <limits>
#include <numeric>
#include <stdexcept>
#include <string>

namespace aletheia {

auto Rational::from_double(double d) -> Rational {
    // Wire-boundary input bounds (R19 cluster G 2026-05-09): cross-binding
    // parity with Python `float_to_rational` and Go `floatToRational` /
    // `doubleToRational`, which both reject NaN / Inf / int64-overflow.
    // Every YAML / Excel / JSON entry-point in C++ funnels through this
    // function, so a single check here covers all 28 callsites.  Outer
    // parser catches (yaml.cpp:230, excel.cpp:489, json_parse.cpp:686+)
    // already convert `std::runtime_error` into `Result<>` error.
    if (std::isnan(d) || std::isinf(d))
        throw std::runtime_error("cannot convert " + std::to_string(d) + " to rational");

    // Integer fast path (covers all whole-number thresholds like 220.0, 300.0).
    auto as_int = static_cast<std::int64_t>(d);
    if (static_cast<double>(as_int) == d)
        return Rational{as_int, 1};

    // Fixed-point scaling: multiply by 10^9, round, then GCD-reduce.
    // This produces human-friendly rationals (0.1 → 1/10, 11.5 → 23/2)
    // rather than exact IEEE 754 binary fractions (0.1 → 3602879701896397/
    // 36028797018963968). All practical user-specified thresholds are "nice"
    // decimal numbers where this gives the expected result.
    constexpr std::int64_t scale = 1'000'000'000;
    const auto scaled = d * static_cast<double>(scale);
    constexpr auto int64_max_d = static_cast<double>(std::numeric_limits<std::int64_t>::max());
    constexpr auto int64_min_d = static_cast<double>(std::numeric_limits<std::int64_t>::min());
    if (scaled > int64_max_d || scaled < int64_min_d)
        throw std::runtime_error("value " + std::to_string(d) +
                                 " overflows int64 when scaled to rational");

    auto num = static_cast<std::int64_t>(std::llround(scaled));
    auto g = std::gcd(std::abs(num), scale);
    auto den = scale / g;
    num /= g;
    if (den < 0) {
        num = -num;
        den = -den;
    }
    return Rational{num, den};
}

} // namespace aletheia
