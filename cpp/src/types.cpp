// SPDX-License-Identifier: BSD-2-Clause
// Rational::from_double — converts a double to an exact Rational.
#include <aletheia/types.hpp>

#include <cmath>
#include <cstdint>
#include <numeric>

namespace aletheia {

auto Rational::from_double(double d) -> Rational {
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
    auto num = static_cast<std::int64_t>(std::llround(d * static_cast<double>(scale)));
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
