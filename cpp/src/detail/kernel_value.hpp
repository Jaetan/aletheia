// SPDX-FileCopyrightText: 2025 Nicolas Pelletier
// SPDX-License-Identifier: BSD-2-Clause
//
// The values the kernel answers, stored as they came, and the words a value
// crosses the C boundary in. The kernel's rationals are its standard library's,
// reduced by their type and over a denominator its proofs hold positive, so a
// reader stores one with no check and no reduction.

#pragma once

#include <aletheia/types.hpp>

#include "ffi_abi.hpp"

#include <cstdint>

namespace aletheia::detail {

// The one way past the checks of Rational and of the identifiers, for a value
// the kernel built and proved.
struct KernelValue {
    // The rational the kernel wrote: reduced, its denominator positive and a
    // zero unsigned, each by the kernel's proof.
    [[nodiscard]] static constexpr auto rational(bool negative, unsigned __int128 numerator,
                                                 unsigned __int128 denominator) -> Rational {
        return Rational{negative, numerator, denominator, Rational::Unchecked{}};
    }

    // The identifiers the kernel wrote at the width their flag names, each
    // within its 11 or 29 bits by the kernel's proof.
    [[nodiscard]] static constexpr auto standard_id(std::uint16_t value) -> StandardId {
        return StandardId{value};
    }
    [[nodiscard]] static constexpr auto extended_id(std::uint32_t value) -> ExtendedId {
        return ExtendedId{value};
    }
};

// A magnitude as the two words the entries read, the low word first.
[[nodiscard]] constexpr auto wire_uint128(unsigned __int128 value) -> FfiUint128 {
    return {.lo = static_cast<std::uint64_t>(value),
            .hi = static_cast<std::uint64_t>(value >> 64U)};
}

// The magnitude two words an entry wrote denote.
[[nodiscard]] constexpr auto uint128_of(FfiUint128 words) -> unsigned __int128 {
    return (static_cast<unsigned __int128>(words.hi) << 64U) | words.lo;
}

// A rational as the structure the entries read; a Rational's zero is unsigned,
// so its sign byte is 0.
[[nodiscard]] constexpr auto wire_rational(Rational const& r) -> FfiRational {
    return {.numerator = wire_uint128(r.numerator()),
            .denominator = wire_uint128(r.denominator()),
            .negative = static_cast<std::uint8_t>(r.negative() ? 1 : 0)};
}

// The rational an entry wrote, which the library writes reduced, over a
// positive denominator and with a zero unsigned; any sign byte but 0 is
// negative.
[[nodiscard]] constexpr auto rational_of(FfiRational const& wire) -> Rational {
    return KernelValue::rational(wire.negative != 0, uint128_of(wire.numerator),
                                 uint128_of(wire.denominator));
}

} // namespace aletheia::detail
