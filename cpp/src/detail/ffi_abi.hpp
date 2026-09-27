// SPDX-FileCopyrightText: 2025 Nicolas Pelletier
// SPDX-License-Identifier: BSD-2-Clause
//
// The structures the kernel's C entry points take by pointer, mirrored from
// haskell-shim/include/aletheia.h (the C++ package does not ship that header).  The unit
// tests compile both and hold every size and offset here equal to the
// header's.

#pragma once

#include <cstdint>

namespace aletheia::detail {

// ALETHEIA_ABI_VERSION: the version of the structures and signatures this
// binding lays out. The backend and the renderer refuse a library reporting any
// other.
inline constexpr std::uint32_t abi_version = 1;

// The entry `dlsym` resolved, as the function type the kernel exports it at.
// dlsym answers void*, and POSIX guarantees a function pointer survives the
// round trip through it on every platform with dlopen; this is the one place
// the conversion is written.
template<typename Fn>
[[nodiscard]] auto symbol_as(void* sym) -> Fn {
    // NOLINTNEXTLINE(cppcoreguidelines-pro-type-reinterpret-cast)
    return reinterpret_cast<Fn>(sym);
}

// struct aletheia_frame: one CAN frame.
struct FfiFrame {
    std::uint64_t timestamp;
    const std::uint8_t* data;
    std::uint32_t can_id;
    std::uint8_t extended;
    std::uint8_t dlc;
    std::uint8_t data_len;
    std::uint8_t brs_present;
    std::uint8_t brs_value;
    std::uint8_t esi_present;
    std::uint8_t esi_value;
};

// struct aletheia_signal_values: count parallel signal indices and rationals.
struct FfiSignalValues {
    const std::uint32_t* indices;
    const std::int64_t* numerators;
    const std::int64_t* denominators;
    std::uint32_t count;
};

// struct aletheia_buffer: a binary result, or the error the kernel set.
struct FfiBuffer {
    std::uint8_t* data;
    char* err;
    std::uint32_t size;
};

// struct aletheia_rational: an exact rational.
struct FfiRational {
    std::int64_t numerator;
    std::int64_t denominator;
};

// struct aletheia_decimal: a parsed decimal, or the error envelope the parser
// set.
struct FfiDecimal {
    FfiRational value;
    char* err;
};

} // namespace aletheia::detail
