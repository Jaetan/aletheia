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

namespace aletheia {

// ---------------------------------------------------------------------------
// Strong typedef templates
// ---------------------------------------------------------------------------

// Prevents implicit mixing of semantically distinct types that share a
// representation. A ScaleFactor is not a PhysicalValue, even though both
// are double underneath.
template<typename Tag, typename T>
class Strong {
    T value_;

public:
    constexpr explicit Strong(T v) : value_(std::move(v)) {}
    [[nodiscard]] constexpr auto get() const -> const T& { return value_; }
    auto operator<=>(const Strong&) const = default;
    bool operator==(const Strong&) const = default;
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
    bool operator==(const StrongString&) const = default;
};

// ---------------------------------------------------------------------------
// Name types (all std::string underneath, all distinct)
// ---------------------------------------------------------------------------

using SignalName = StrongString<struct SignalNameTag>;
using MessageName = StrongString<struct MessageNameTag>;
using NodeName = StrongString<struct NodeNameTag>;
using Unit = StrongString<struct UnitTag>;

// ---------------------------------------------------------------------------
// Numeric physical types (all double underneath, all distinct)
// ---------------------------------------------------------------------------

// Physical measurement domain (signal readouts, thresholds, min/max bounds)
using PhysicalValue = Strong<struct PhysicalValueTag, double>;
// DBC signal scaling parameters (not physical values)
using ScaleFactor = Strong<struct ScaleFactorTag, double>;
using ScaleOffset = Strong<struct ScaleOffsetTag, double>;
// Absolute change magnitude for ChangedBy predicates
using Delta = Strong<struct DeltaTag, double>;

// ---------------------------------------------------------------------------
// Integer domain types (distinct bit-level types)
// ---------------------------------------------------------------------------

using BitPosition = Strong<struct BitPositionTag, std::uint16_t>;
using BitLength = Strong<struct BitLengthTag, std::uint8_t>;
using PropertyIndex = Strong<struct PropertyIndexTag, std::size_t>;
using MultiplexValue = Strong<struct MultiplexValueTag, std::uint32_t>;

// ---------------------------------------------------------------------------
// Frame payload: raw bytes, not interpreted
// ---------------------------------------------------------------------------

using FramePayload = std::array<std::byte, 8>;

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
    bool operator==(const StandardId&) const = default;
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
    bool operator==(const ExtendedId&) const = default;
};

using CanId = std::variant<StandardId, ExtendedId>;

// ---------------------------------------------------------------------------
// Timestamp: microseconds since trace start (chrono, not bare integer)
// ---------------------------------------------------------------------------

using Timestamp = std::chrono::microseconds;

// ---------------------------------------------------------------------------
// DLC: 0-8, validated at construction
// ---------------------------------------------------------------------------

class Dlc {
    std::uint8_t value_;
    explicit constexpr Dlc(std::uint8_t v) : value_(v) {}

public:
    static constexpr auto create(std::uint8_t v) -> std::expected<Dlc, std::string> {
        if (v > 8)
            return std::unexpected("DLC must be 0-8");
        return Dlc{v};
    }
    [[nodiscard]] constexpr auto value() const -> std::uint8_t { return value_; }
    auto operator<=>(const Dlc&) const = default;
    bool operator==(const Dlc&) const = default;
};

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

} // namespace aletheia
