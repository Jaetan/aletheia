// SPDX-FileCopyrightText: 2025 Nicolas Pelletier
// SPDX-License-Identifier: BSD-2-Clause
//
// The structures the kernel's C entry points take by pointer, mirrored from
// haskell-shim/include/aletheia.h (the C++ package does not ship that header).  The unit
// tests compile both and hold every size and offset here equal to the
// header's.

#pragma once

#include <cstddef>
#include <cstdint>
#include <string_view>

namespace aletheia::detail {

// ALETHEIA_ABI_VERSION: the version of the structures and signatures this
// binding lays out. The backend and the renderer refuse a library reporting any
// other.
inline constexpr std::uint32_t abi_version = 4;

// The entry `dlsym` resolved, as the function type the kernel exports it at.
// dlsym answers void*, and POSIX guarantees a function pointer survives the
// round trip through it on every platform with dlopen; this is the one place
// the conversion is written.
template<typename Fn>
[[nodiscard]] auto symbol_as(void* sym) -> Fn {
    // NOLINTNEXTLINE(cppcoreguidelines-pro-type-reinterpret-cast)
    return reinterpret_cast<Fn>(sym);
}

// struct aletheia_text: size bytes of UTF-8 from data, with no terminating NUL.
struct FfiText {
    char const* data;
    std::size_t size;
};

// The text a view spans, which the kernel reads whole: a NUL among its bytes
// is the kernel's to refuse, not the end of the text.
[[nodiscard]] constexpr auto ffi_text(std::string_view s) noexcept -> FfiText {
    return {.data = s.data(), .size = s.size()};
}

// struct aletheia_frame: one CAN frame.
struct FfiFrame {
    std::uint64_t timestamp;
    std::uint8_t const* data;
    std::uint32_t can_id;
    std::uint8_t extended;
    std::uint8_t dlc;
    std::uint8_t data_len;
    std::uint8_t brs_present;
    std::uint8_t brs_value;
    std::uint8_t esi_present;
    std::uint8_t esi_value;
};

// struct aletheia_uint128: an unsigned 128-bit magnitude, low word first.
struct FfiUint128 {
    std::uint64_t lo;
    std::uint64_t hi;
};

// struct aletheia_rational: an exact rational, a sign and two magnitudes; the
// sign is 0 when the numerator is 0.
struct FfiRational {
    FfiUint128 numerator;
    FfiUint128 denominator;
    std::uint8_t negative;
};

// struct aletheia_signal_values: count signal indices and their values.
struct FfiSignalValues {
    std::uint32_t const* indices;
    FfiRational const* values;
    std::uint32_t count;
};

// struct aletheia_buffer: a binary result, or the error the kernel set.
struct FfiBuffer {
    std::uint8_t* data;
    char* err;
    std::uint32_t size;
};

// struct aletheia_decimal: a parsed decimal, or the error envelope the parser
// set.
struct FfiDecimal {
    FfiRational value;
    char* err;
};

// struct aletheia_time_bound: a time bound's whole microseconds, or the error
// envelope the kernel set.
struct FfiTimeBound {
    std::uint64_t microseconds;
    char* err;
};

// struct aletheia_property_check: the kernel's refusal of a property, or null.
struct FfiPropertyCheck {
    char* err;
};

} // namespace aletheia::detail
