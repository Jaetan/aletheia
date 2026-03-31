// SPDX-License-Identifier: BSD-2-Clause
#pragma once

#include <array>
#include <chrono>
#include <compare>
#include <cstddef>
#include <cstdint>
#include <expected>
#include <string>
#include <string_view>
#include <utility>
#include <variant>
#include <vector>

namespace aletheia {

// ---------------------------------------------------------------------------
// Strong typedef templates
// ---------------------------------------------------------------------------

// Prevents implicit mixing of semantically distinct types that share a
// representation. A RationalFactor is not a PhysicalValue, even though
// both carry numeric values.
template<typename Tag, typename T>
class Strong {
    T value_;

public:
    constexpr explicit Strong(T v) : value_(std::move(v)) {}
    [[nodiscard]] constexpr auto get() const -> const T& { return value_; }
    auto operator<=>(const Strong&) const = default;
};

// String strong types add implicit string_view conversion for ergonomic use
// in logging and formatting, while still preventing implicit mixing.
template<typename Tag>
class StrongString {
    std::string value_;

public:
    explicit StrongString(std::string v) : value_(std::move(v)) {}
    [[nodiscard]] auto get() const -> const std::string& { return value_; }
    // NOLINTNEXTLINE(google-explicit-constructor,hicpp-explicit-conversions)
    [[nodiscard]] operator std::string_view() const noexcept { return value_; }
    auto operator<=>(const StrongString&) const = default;
};

// ---------------------------------------------------------------------------
// Name types (all std::string underneath, all distinct)
// ---------------------------------------------------------------------------

using SignalName = StrongString<struct SignalNameTag>;
using MessageName = StrongString<struct MessageNameTag>;
using NodeName = StrongString<struct NodeNameTag>;
using Unit = StrongString<struct UnitTag>;

// ---------------------------------------------------------------------------
// Numeric physical types (double underneath, distinct)
// ---------------------------------------------------------------------------

// Physical measurement domain (signal readouts, thresholds)
using PhysicalValue = Strong<struct PhysicalValueTag, double>;
// Absolute change magnitude for ChangedBy predicates
using Delta = Strong<struct DeltaTag, double>;

// ---------------------------------------------------------------------------
// Rational: exact numerator/denominator (for DBC signal parameters)
// ---------------------------------------------------------------------------

struct Rational {
    std::int64_t numerator = 0;
    std::int64_t denominator = 1; // always > 0

    [[nodiscard]] constexpr auto to_double() const -> double {
        return static_cast<double>(numerator) / static_cast<double>(denominator);
    }

    // Cross-multiply comparison (avoids floating-point).
    constexpr auto operator<=>(const Rational& rhs) const {
        // a/b <=> c/d  iff  a*d <=> c*b  (denominators always positive)
        auto lhs_prod = static_cast<__int128>(numerator) * rhs.denominator;
        auto rhs_prod = static_cast<__int128>(rhs.numerator) * denominator;
        return lhs_prod <=> rhs_prod;
    }
    constexpr bool operator==(const Rational& rhs) const {
        return (*this <=> rhs) == std::strong_ordering::equal;
    }
};

// DBC signal scaling parameters — stored as exact rationals.
// PhysicalValue (double) remains for predicate thresholds and extraction results.
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

public:
    static constexpr auto create(std::uint16_t v) -> std::expected<StandardId, std::string> {
        if (v > 2047)
            return std::unexpected("Standard CAN ID must be 0-2047");
        return StandardId{v};
    }
    [[nodiscard]] constexpr auto value() const -> std::uint16_t { return value_; }
    auto operator<=>(const StandardId&) const = default;
};

class ExtendedId {
    std::uint32_t value_;
    explicit constexpr ExtendedId(std::uint32_t v) : value_(v) {}

public:
    static constexpr auto create(std::uint32_t v) -> std::expected<ExtendedId, std::string> {
        if (v > 536'870'911)
            return std::unexpected("Extended CAN ID must be 0-536870911");
        return ExtendedId{v};
    }
    [[nodiscard]] constexpr auto value() const -> std::uint32_t { return value_; }
    auto operator<=>(const ExtendedId&) const = default;
};

using CanId = std::variant<StandardId, ExtendedId>;

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
            return Dlc::create(code).value();
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
    PhysicalValue value{0.0};
};

// ---------------------------------------------------------------------------
// Frame: bundles all parameters for send_frame / send_frames
// ---------------------------------------------------------------------------

struct Frame {
    Timestamp timestamp;
    CanId id;
    Dlc dlc;
    FramePayload data;
};

} // namespace aletheia
