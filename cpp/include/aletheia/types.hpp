// SPDX-FileCopyrightText: 2025 Nicolas Pelletier
// SPDX-License-Identifier: BSD-2-Clause
#pragma once

#include <array>
#include <chrono>
#include <compare>
#include <concepts>
#include <cstddef>
#include <cstdint>
#include <expected>
#include <optional>
#include <stdexcept>
#include <string>
#include <string_view>
#include <utility>
#include <variant>
#include <vector>

namespace aletheia {

// ---------------------------------------------------------------------------
// Strong typedef template
// ---------------------------------------------------------------------------

// Prevents implicit mixing of semantically distinct types that share a
// representation. A RationalFactor is not a PhysicalValue, even though
// both carry numeric values.
//
// `of(...)` is a perfect-forwarding factory: `PhysicalValue::of(1, 10)`
// instead of `PhysicalValue{Rational{1, 10}}`. R20 CPP-D-15.2 chose this
// over per-tag free `make_*` factories so the convenience scales to every
// Strong instantiation without N new symbols.
//
// String specialization: when `T == std::string`, also exposes an
// explicit `operator std::string_view()` so log/format sites can write
// `std::string_view{name}` without copying. Concept-gated so non-string
// strongs can't accidentally convert. R20 CPP-D-15.3 merged the
// previously-separate `StrongString<Tag>` into this single template.
template<typename Tag, typename T>
class Strong {
    T value_;

public:
    constexpr explicit Strong(T v) : value_(std::move(v)) {}

    template<typename... Args>
        requires std::constructible_from<T, Args...>
    static constexpr auto of(Args&&... args) -> Strong {
        return Strong(T(std::forward<Args>(args)...));
    }

    [[nodiscard]] constexpr auto get() const -> const T& { return value_; }

    [[nodiscard]] explicit operator std::string_view() const noexcept
        requires std::same_as<T, std::string>
    {
        return value_;
    }

    auto operator<=>(const Strong&) const = default;
};

// ---------------------------------------------------------------------------
// Name types (all std::string underneath, all distinct)
// ---------------------------------------------------------------------------

using SignalName = Strong<struct SignalNameTag, std::string>;
using MessageName = Strong<struct MessageNameTag, std::string>;
using NodeName = Strong<struct NodeNameTag, std::string>;
using Unit = Strong<struct UnitTag, std::string>;

// ---------------------------------------------------------------------------
// Rational: exact numerator/denominator
// ---------------------------------------------------------------------------

// Exact rational with the invariant `den_ > 0`, enforced by every ctor +
// factory.  Class (not struct) per R23 — CPP-D-15.1: a public-fields
// struct invites direct writes that would bypass the invariant; private
// fields + `numerator()` / `denominator()` accessors make `den_ > 0` a
// type-level guarantee rather than a callsite discipline.
class Rational {
public:
    constexpr Rational() = default;
    constexpr Rational(std::int64_t n, std::int64_t d) : num_(n), den_(d) {
        // The bare `assert` would disappear under -DNDEBUG (the default Release
        // CMake mode); throwing keeps the invariant enforced at every callsite
        // so a Release-build hot-path call cannot silently accept den == 0 or
        // den < 0.  Use Rational::make for fallible (returns std::expected)
        // construction in untrusted-input contexts.  R19 cluster 12 — CPP-B-7.1.
        if (d <= 0) {
            throw std::invalid_argument("Rational: denominator must be positive (was " +
                                        std::to_string(d) + ")");
        }
    }

    [[nodiscard]] constexpr auto numerator() const -> std::int64_t { return num_; }
    [[nodiscard]] constexpr auto denominator() const -> std::int64_t { return den_; }

    [[nodiscard]] constexpr auto to_double() const -> double {
        return static_cast<double>(num_) / static_cast<double>(den_);
    }

    // Cross-multiply comparison (avoids floating-point).
    // __int128 is a GCC/Clang extension (not standard C++); the project targets
    // g++ >= 14 and clang >= 21 on Linux only, where it is always available.
    // A double-precision fallback would silently lose precision on large
    // numerator/denominator pairs, so we refuse to build rather than ship it.
    static_assert(sizeof(__int128) >= 16, "Aletheia requires __int128 support "
                                          "(g++ >= 14 / clang >= 21 on Linux).");
    constexpr auto operator<=>(const Rational& rhs) const {
        // a/b <=> c/d  iff  a*d <=> c*b  (denominators always positive)
        auto lhs_prod = static_cast<__int128>(num_) * rhs.den_;
        auto rhs_prod = static_cast<__int128>(rhs.num_) * den_;
        return lhs_prod <=> rhs_prod;
    }
    constexpr bool operator==(const Rational& rhs) const {
        return (*this <=> rhs) == std::strong_ordering::equal;
    }

    // Validated factory: returns an error if denominator is not positive.
    // Use for untrusted input; direct construction throws in every mode.
    static constexpr auto make(std::int64_t num, std::int64_t den)
        -> std::expected<Rational, std::string> {
        if (den <= 0)
            return std::unexpected("Rational denominator must be positive");
        return Rational{num, den};
    }

    // Parse a decimal literal into an exact Rational via the Agda kernel's
    // decimal SSOT (`aletheia_parse_decimal`) — the float principle: a decimal
    // is an exact rational (denominator 2^a*5^b), never a float64. The grammar
    // is the kernel's: `-?digits` or `-?digits.digits+` (no `+` sign, no
    // leading/trailing `.`, no exponent). RTS-gated and vocal: an FfiBackend
    // must be live first (it is the sole GHC RTS initialiser), else this throws
    // `AletheiaException(Ffi)` rather than self-initialising. Throws
    // `AletheiaException(Validation)` on a malformed literal or int64 overflow.
    static auto from_decimal(std::string_view s) -> Rational;

private:
    std::int64_t num_ = 0;
    std::int64_t den_ = 1;
};

// ---------------------------------------------------------------------------
// Numeric physical types
// ---------------------------------------------------------------------------

// Physical measurement domain (signal readouts, thresholds).
// Uses Rational for exact precision — Agda sends signal values as
// {numerator, denominator} pairs; double would lose precision on 1/3, 1/7 etc.
using PhysicalValue = Strong<struct PhysicalValueTag, Rational>;
// Signed change threshold for ChangedBy predicates (sign determines direction).
// R19 cluster 7 — CPP-D-19.2: cross-binding parity with Python (Fraction)
// and Go (Rational) — was double, now Rational so the wire-shape is
// numerator/denominator-exact across all three bindings.
using Delta = Strong<struct DeltaTag, Rational>;
// Absolute tolerance for StableWithin predicates (Rational for the same reason).
using Tolerance = Strong<struct ToleranceTag, Rational>;

// DBC signal scaling parameters — stored as exact rationals.
using RationalFactor = Strong<struct RationalFactorTag, Rational>;
using RationalOffset = Strong<struct RationalOffsetTag, Rational>;
using RationalBound = Strong<struct RationalBoundTag, Rational>;

// ---------------------------------------------------------------------------
// Integer domain types (distinct bit-level types)
// ---------------------------------------------------------------------------

using BitPosition = Strong<struct BitPositionTag, std::uint16_t>;
using BitLength = Strong<struct BitLengthTag, std::uint8_t>;
using PropertyIndex = Strong<struct PropertyIndexTag, std::size_t>;
using MultiplexValue = Strong<struct MultiplexValueTag, std::uint32_t>;

// ---------------------------------------------------------------------------
// Frame payload: variable-length raw bytes (up to 64 for CAN-FD)
// ---------------------------------------------------------------------------

using FramePayload = std::vector<std::byte>;

// ---------------------------------------------------------------------------
// CAN ID: two variants, validated at construction
// ---------------------------------------------------------------------------

class StandardId {
    std::uint16_t value_;
    explicit constexpr StandardId(std::uint16_t v) : value_(v) {}

    static constexpr std::uint16_t max_id = (1U << 11U) - 1; // 11-bit CAN ID

public:
    static constexpr auto create(std::uint16_t v) -> std::expected<StandardId, std::string> {
        if (v > max_id)
            return std::unexpected("Standard CAN ID must be 0-2047");
        return StandardId{v};
    }
    [[nodiscard]] constexpr auto value() const -> std::uint16_t { return value_; }
    auto operator<=>(const StandardId&) const = default;
};

class ExtendedId {
    std::uint32_t value_;
    explicit constexpr ExtendedId(std::uint32_t v) : value_(v) {}

    static constexpr std::uint32_t max_id = (1U << 29U) - 1; // 29-bit CAN ID

public:
    static constexpr auto create(std::uint32_t v) -> std::expected<ExtendedId, std::string> {
        if (v > max_id)
            return std::unexpected("Extended CAN ID must be 0-536870911");
        return ExtendedId{v};
    }
    [[nodiscard]] constexpr auto value() const -> std::uint32_t { return value_; }
    auto operator<=>(const ExtendedId&) const = default;
};

using CanId = std::variant<StandardId, ExtendedId>;

/// Extract the underlying 11- or 29-bit value from a CanId, regardless
/// of standard vs extended discrimination.  Replaces the
/// `std::visit([](const auto& v) -> std::uint32_t { return v.value(); }, id)`
/// pattern repeated across the source tree (R19 cluster 14 / CPP-A-6.2).
[[nodiscard]] constexpr auto can_id_value(const CanId& id) -> std::uint32_t {
    return std::visit([](const auto& v) -> std::uint32_t { return v.value(); }, id);
}

/// Returns true when the CanId carries an `ExtendedId` (29-bit) variant,
/// false for `StandardId` (11-bit).  Replaces
/// `std::holds_alternative<ExtendedId>(id)` site-by-site (R19 cluster 14
/// / CPP-A-6.2).
[[nodiscard]] constexpr auto can_id_is_extended(const CanId& id) -> bool {
    return std::holds_alternative<ExtendedId>(id);
}

// ---------------------------------------------------------------------------
// Timestamp: microseconds since trace start (chrono, not bare integer)
// ---------------------------------------------------------------------------

using Timestamp = std::chrono::microseconds;

// ---------------------------------------------------------------------------
// DLC: 0-15 (CAN-FD), validated at construction
// ---------------------------------------------------------------------------

class Dlc {
    std::uint8_t value_;
    explicit constexpr Dlc(std::uint8_t v) : value_(v) {}

public:
    static constexpr auto create(std::uint8_t v) -> std::expected<Dlc, std::string> {
        if (v > 15)
            return std::unexpected("DLC must be 0-15");
        return Dlc{v};
    }
    [[nodiscard]] constexpr auto value() const -> std::uint8_t { return value_; }
    auto operator<=>(const Dlc&) const = default;
};

// CAN-FD DLC to payload byte count mapping.
// DLC 0-8 maps directly; 9→12, 10→16, 11→20, 12→24, 13→32, 14→48, 15→64.
constexpr auto dlc_to_bytes(Dlc dlc) -> std::size_t {
    constexpr std::array<std::size_t, 16> table = {0, 1,  2,  3,  4,  5,  6,  7,
                                                   8, 12, 16, 20, 24, 32, 48, 64};
    return table[dlc.value()];
}

// Payload byte count to DLC code.
// Returns the DLC code for a valid CAN/CAN-FD payload size, or an error.
inline auto bytes_to_dlc(std::size_t byte_count) -> std::expected<Dlc, std::string> {
    constexpr std::array<std::pair<std::size_t, std::uint8_t>, 16> table = {{
        {0, 0},
        {1, 1},
        {2, 2},
        {3, 3},
        {4, 4},
        {5, 5},
        {6, 6},
        {7, 7},
        {8, 8},
        {12, 9},
        {16, 10},
        {20, 11},
        {24, 12},
        {32, 13},
        {48, 14},
        {64, 15},
    }};
    for (auto [bytes, code] : table)
        if (bytes == byte_count)
            return *Dlc::create(code);
    return std::unexpected("invalid DLC byte count: " + std::to_string(byte_count));
}

// ---------------------------------------------------------------------------
// Byte order
// ---------------------------------------------------------------------------

enum class ByteOrder { LittleEndian, BigEndian };

// ---------------------------------------------------------------------------
// Signal value: name + physical value
// ---------------------------------------------------------------------------

struct SignalValue {
    SignalName name;
    PhysicalValue value{Rational{}};
};

// ---------------------------------------------------------------------------
// Frame: bundles all parameters for send_frame / send_frames
// ---------------------------------------------------------------------------

struct Frame {
    Timestamp timestamp;
    CanId id;
    Dlc dlc;
    FramePayload data;
    // CAN-FD Bit Rate Switch (ISO 11898-1:2015 §10.4.2): set for CAN-FD
    // frames carrying the bit, std::nullopt for CAN 2.0B frames where it
    // does not exist on the wire.  The Aletheia kernel does not consume
    // BRS — pass-through metadata for binding consumers and the JSON wire
    // shape (R19P2 cluster 18 — AGDA-D-10.1 closure).
    std::optional<bool> brs;
    // CAN-FD Error State Indicator (ISO 11898-1:2015 §10.4.3); same
    // semantics + pass-through status as brs.
    std::optional<bool> esi;
};

} // namespace aletheia
