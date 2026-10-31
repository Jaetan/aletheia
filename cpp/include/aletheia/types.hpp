// SPDX-FileCopyrightText: 2025 Nicolas Pelletier
// SPDX-License-Identifier: BSD-2-Clause
#pragma once

#include <aletheia/error.hpp>

#include <algorithm>
#include <array>
#include <chrono>
#include <compare>
#include <concepts>
#include <cstddef>
#include <cstdint>
#include <expected>
#include <format>
#include <limits>
#include <numeric>
#include <optional>
#include <string>
#include <string_view>
#include <type_traits>
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
// instead of `PhysicalValue{Rational{1, 10}}`. This form is preferred
// over per-tag free `make_*` factories so the convenience scales to every
// Strong instantiation without N new symbols.
//
// String specialization: when `T == std::string`, also exposes an
// explicit `operator std::string_view()` so log/format sites can write
// `std::string_view{name}` without copying. Concept-gated so non-string
// strongs can't accidentally convert.
template<typename Tag, typename T>
class Strong {
    T value_;

public:
    constexpr explicit Strong(T v) : value_(std::move(v)) {}

    template<typename... Args>
        requires std::constructible_from<T, Args...>
    [[nodiscard]] static constexpr auto of(Args&&... args) -> Strong {
        return Strong(T(std::forward<Args>(args)...));
    }

    [[nodiscard]] constexpr auto get() const -> T const& { return value_; }

    [[nodiscard]] explicit operator std::string_view() const noexcept
        requires std::same_as<T, std::string>
    {
        return value_;
    }

    auto operator<=>(Strong const&) const = default;
};

// ---------------------------------------------------------------------------
// Name types (all std::string underneath, all distinct)
// ---------------------------------------------------------------------------

using SignalName = Strong<struct SignalNameTag, std::string>;
using MessageName = Strong<struct MessageNameTag, std::string>;
using NodeName = Strong<struct NodeNameTag, std::string>;
using Unit = Strong<struct UnitTag, std::string>;

// ---------------------------------------------------------------------------
// Rational: exact sign, numerator and denominator
// ---------------------------------------------------------------------------

namespace detail {
// The readers' way to the values the kernel built and proved: a Rational
// reduced with a positive denominator, an identifier within its width.
// Defined where the readers live.
struct KernelValue;
} // namespace detail

// Exact rational: a sign, a numerator magnitude and a denominator, each
// magnitude reaching 2^128-1 as the kernel's numbers do. Every factory stores
// the value reduced, with a denominator of at least 1 and a zero unsigned, so
// two Rationals are equal exactly when their fields are. Private fields keep
// those facts a property of the type rather than of each call site.
class Rational {
public:
    constexpr Rational() = default;

    // Exact-numeric boundary, the float principle: a `double` must not narrow
    // silently into a component, and a `bool` must not pass as a number, so the
    // parameters are non-bool integral types and a decimal goes through
    // `Rational::from_decimal` (the kernel decimal SSOT). Constant expressions
    // only: a literal whose denominator is not positive fails the build, and a
    // pair known at run time goes through `make` or `integer`.
    template<std::integral N, std::integral D>
        requires(!std::same_as<N, bool> && !std::same_as<D, bool>)
    consteval Rational(N n, D d) : Rational(make(n, d).value()) {}

    [[nodiscard]] constexpr auto negative() const -> bool { return negative_; }
    [[nodiscard]] constexpr auto numerator() const -> unsigned __int128 { return num_; }
    [[nodiscard]] constexpr auto denominator() const -> unsigned __int128 { return den_; }

    constexpr auto operator==(Rational const&) const -> bool = default;

    // The value a sign and two magnitudes denote, reduced, or a Validation
    // error for a zero denominator.
    [[nodiscard]] static constexpr auto make(bool negative, unsigned __int128 numerator,
                                             unsigned __int128 denominator) -> Result<Rational> {
        if (denominator == 0)
            return detail::validation_refusal("Rational denominator must be positive");
        return reduced(negative, numerator, denominator);
    }

    // The value `num / den`, reduced, or a Validation error for a denominator
    // that is not positive.
    template<std::integral N, std::integral D>
        requires(!std::same_as<N, bool> && !std::same_as<D, bool>)
    [[nodiscard]] static constexpr auto make(N num, D den) -> Result<Rational> {
        if (std::cmp_less_equal(den, 0))
            return detail::validation_refusal("Rational denominator must be positive");
        return reduced(num < 0, magnitude(num), static_cast<unsigned __int128>(den));
    }

    // The whole number `n / 1`, which cannot fail: every integral type up to
    // 128 bits holds only values the type carries. A `bool` or a `double` does
    // not compile.
    template<std::integral I>
        requires(!std::same_as<I, bool>)
    [[nodiscard]] static constexpr auto integer(I n) -> Rational {
        return Rational{n < 0, magnitude(n), 1, Unchecked{}};
    }

    // Parse a decimal literal into an exact Rational via the Agda kernel's
    // decimal SSOT (`aletheia_parse_decimal`), the float principle: a decimal
    // is an exact rational (denominator 2^a*5^b), never a float64. The grammar
    // is the kernel's: `-?digits` or `-?digits.digits+` (no `+` sign, no
    // leading/trailing `.`, no exponent). The GHC runtime must be up
    // (`aletheia::start_runtime` or a backend), else this returns an error of
    // kind Ffi rather than starting it. A refusal is the kernel's, decoded by
    // `detail::binary_refusal`: the literal is the caller's own text, so a malformed
    // one is kind Validation with code `TextParseFailure` or
    // `TextTrailingInput` (`FfiValidationError` when the shared library refused
    // the bytes before the kernel read them), and a component past the kernel's
    // magnitude bound is kind InputBoundExceeded with `bound_info()`. A wire
    // fault is kind Protocol.
    [[nodiscard]] static auto from_decimal(std::string_view s) -> Result<Rational>;

private:
    friend struct detail::KernelValue;

    // The stores, reached once the fields are known reduced, the denominator
    // positive and a zero unsigned.
    struct Unchecked {};
    constexpr Rational(bool negative, unsigned __int128 num, unsigned __int128 den,
                       Unchecked /*unchecked*/)
        : num_(num)
        , den_(den)
        , negative_(negative) {}

    // The magnitude of `n`, exact for every value of every integral type up to
    // 128 bits, the most negative included.
    template<std::integral I>
    [[nodiscard]] static constexpr auto magnitude(I n) -> unsigned __int128 {
        auto const wide = static_cast<unsigned __int128>(n);
        return n < 0 ? static_cast<unsigned __int128>(0) - wide : wide;
    }

    [[nodiscard]] static constexpr auto reduced(bool negative, unsigned __int128 num,
                                                unsigned __int128 den) -> Rational {
        auto const g = std::gcd(num, den);
        return Rational{negative && num != 0, num / g, den / g, Unchecked{}};
    }

    unsigned __int128 num_ = 0;
    unsigned __int128 den_ = 1;
    bool negative_ = false;
};

// A whole number as a sign and a magnitude reaching 2^128-1: a value
// description's key. Printed through `std::format`, a zero reads unsigned
// whatever `negative` says.
struct SignMagnitude {
    bool negative = false;
    unsigned __int128 magnitude = 0;

    // The value as an int64, or nullopt when it lies outside int64.
    [[nodiscard]] constexpr auto to_int64() const -> std::optional<std::int64_t> {
        constexpr auto int64_max =
            static_cast<unsigned __int128>(std::numeric_limits<std::int64_t>::max());
        if (!negative)
            return magnitude <= int64_max ? std::optional{static_cast<std::int64_t>(magnitude)}
                                          : std::nullopt;
        if (magnitude > int64_max + 1)
            return std::nullopt;
        return static_cast<std::int64_t>(static_cast<unsigned __int128>(0) - magnitude);
    }

    constexpr auto operator==(SignMagnitude const&) const -> bool = default;
};

// ---------------------------------------------------------------------------
// Numeric physical types
// ---------------------------------------------------------------------------

// Physical measurement domain (signal readouts, thresholds).
// Uses Rational for exact precision — Agda sends signal values as
// {numerator, denominator} pairs; double would lose precision on 1/3, 1/7 etc.
using PhysicalValue = Strong<struct PhysicalValueTag, Rational>;
// Signed change threshold for ChangedBy predicates (sign determines direction).
// Rational, as Python's Fraction and Go's Rational, so the wire shape is
// numerator/denominator-exact across the bindings.
using Delta = Strong<struct DeltaTag, Rational>;
// Absolute tolerance for StableWithin predicates (Rational for the same reason).
using Tolerance = Strong<struct ToleranceTag, Rational>;

// DBC signal scaling parameters — stored as exact rationals.
using RationalFactor = Strong<struct RationalFactorTag, Rational>;
using RationalOffset = Strong<struct RationalOffsetTag, Rational>;
using RationalBound = Strong<struct RationalBoundTag, Rational>;

// ---------------------------------------------------------------------------
// Compile-time proof of the float principle at the exact-numeric boundary
// ---------------------------------------------------------------------------
// These fire in every translation unit that includes this header, so a
// regression that re-admits a float or bool at a Rational boundary fails the
// build — it cannot be silently skipped the way a unit test can.  `Strong::of`
// is closed transitively by the constrained ctor (its `std::constructible_from`
// guard goes false for a double/bool argument), so it needs no separate edit.
//
// The ctor checks go through the `std::constructible_from` trait (SFINAE-safe at
// namespace scope); `make`/`of` are function calls, so they go through small
// *templated* concepts — a requires-expression is only SFINAE-friendly inside a
// template, whereas a bare non-dependent `requires { ... }` hard-errors on an
// unviable call instead of yielding false.
namespace detail {
template<typename... Args>
concept RationalMakeable = requires { Rational::make(std::declval<Args>()...); };
template<typename StrongT, typename... Args>
concept StrongOfable = requires { StrongT::of(std::declval<Args>()...); };
template<typename I>
concept RationalIntegerable = requires { Rational::integer(std::declval<I>()); };
// A literal pair the constructor accepts: a constant evaluation that fails in a
// template argument is a substitution failure, so a refused literal reads false.
template<auto N, auto D>
concept RationalLiteral =
    requires { typename std::integral_constant<bool, Rational{N, D}.negative()>; };
} // namespace detail

static_assert(std::constructible_from<Rational, int, int>, "integer construction must still work");
static_assert(!std::constructible_from<Rational, double, int>,
              "a double must not narrow into a Rational");
static_assert(!std::constructible_from<Rational, bool, int>,
              "a bool must not pass as a numeric value");
static_assert(detail::RationalMakeable<int, int>, "integer make must still work");
static_assert(!detail::RationalMakeable<double, int>, "a double must not narrow via make");
static_assert(!detail::RationalMakeable<bool, int>, "a bool must not pass through make");
static_assert(detail::StrongOfable<PhysicalValue, int, int>, "integer of(...) must still work");
static_assert(!detail::StrongOfable<PhysicalValue, double, int>, "of(...) must reject a double");
static_assert(!detail::StrongOfable<PhysicalValue, bool, int>, "of(...) must reject a bool");
static_assert(!detail::StrongOfable<RationalFactor, double, int>,
              "DBC factor of(...) must reject a double");
static_assert(detail::RationalIntegerable<int> && detail::RationalIntegerable<std::int64_t> &&
                  detail::RationalIntegerable<std::uint64_t> &&
                  detail::RationalIntegerable<unsigned __int128>,
              "a whole number of every integral type up to 128 bits must build");
static_assert(!detail::RationalIntegerable<double>, "a double must not narrow via integer");
static_assert(!detail::RationalIntegerable<bool>, "a bool must not pass through integer");
static_assert(detail::RationalLiteral<1, 10>, "a literal fraction must build");
static_assert(!detail::RationalLiteral<1, 0>, "a zero denominator must not build");
static_assert(!detail::RationalLiteral<1, -1>, "a negative denominator must not build");
static_assert(detail::RationalLiteral<std::uint64_t{1} << 63U, 1>,
              "a numerator past int64 must build");
static_assert(detail::RationalLiteral<1, std::uint64_t{1} << 63U>,
              "a denominator past int64 must build");
static_assert(Rational{2, 4} == Rational{1, 2}, "a value is stored reduced");
static_assert(Rational{0, 5} == Rational{}, "a zero is stored unsigned over 1");
static_assert(Rational{-3, 6}.negative() && Rational{-3, 6}.numerator() == 1 &&
                  Rational{-3, 6}.denominator() == 2,
              "the sign is its own field, the magnitudes reduced");

// ---------------------------------------------------------------------------
// Integer domain types (distinct bit-level types)
// ---------------------------------------------------------------------------

using BitPosition = Strong<struct BitPositionTag, std::uint16_t>;
using BitLength = Strong<struct BitLengthTag, std::uint16_t>;
using PropertyIndex = Strong<struct PropertyIndexTag, std::size_t>;
using MultiplexValue = Strong<struct MultiplexValueTag, unsigned __int128>;

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
    friend struct detail::KernelValue;

    static constexpr std::uint16_t max_id = (1U << 11U) - 1; // 11-bit CAN ID

public:
    [[nodiscard]] static constexpr auto create(std::uint16_t v) -> Result<StandardId> {
        if (v > max_id)
            return detail::validation_refusal("Standard CAN ID must be 0-2047");
        return StandardId{v};
    }
    [[nodiscard]] constexpr auto value() const -> std::uint16_t { return value_; }
    auto operator<=>(StandardId const&) const = default;
};

class ExtendedId {
    std::uint32_t value_;
    explicit constexpr ExtendedId(std::uint32_t v) : value_(v) {}
    friend struct detail::KernelValue;

    static constexpr std::uint32_t max_id = (1U << 29U) - 1; // 29-bit CAN ID

public:
    [[nodiscard]] static constexpr auto create(std::uint32_t v) -> Result<ExtendedId> {
        if (v > max_id)
            return detail::validation_refusal("Extended CAN ID must be 0-536870911");
        return ExtendedId{v};
    }
    [[nodiscard]] constexpr auto value() const -> std::uint32_t { return value_; }
    auto operator<=>(ExtendedId const&) const = default;
};

using CanId = std::variant<StandardId, ExtendedId>;

/// Extract the underlying 11- or 29-bit value from a CanId, regardless
/// of standard vs extended discrimination, so call sites need not visit
/// the variant themselves.
[[nodiscard]] constexpr auto can_id_value(CanId const& id) -> std::uint32_t {
    return std::visit([](auto const& v) -> std::uint32_t { return v.value(); }, id);
}

/// Returns true when the CanId carries an `ExtendedId` (29-bit) variant,
/// false for `StandardId` (11-bit).
[[nodiscard]] constexpr auto can_id_is_extended(CanId const& id) -> bool {
    return std::holds_alternative<ExtendedId>(id);
}

// ---------------------------------------------------------------------------
// Timestamp: microseconds since trace start (chrono, not bare integer)
// ---------------------------------------------------------------------------

using Timestamp = std::chrono::microseconds;

// Scale out of the microsecond domain: the renderer prints a time bound in
// seconds or milliseconds when it divides evenly (Go `usPerMillisecond`, Rust
// `US_PER_MILLISECOND`).
inline constexpr std::uint64_t us_per_millisecond = 1'000;
inline constexpr std::uint64_t us_per_second = 1'000'000;

// ---------------------------------------------------------------------------
// TimeBound: a time window's bound in whole microseconds
// ---------------------------------------------------------------------------

// A time window's bound in whole microseconds, the kernel's own unit, reaching
// 2^64-1 as the kernel's time bound does. Built from a count
// (`TimeBound{100'000}`) or read from text through the kernel; no chrono
// duration converts into it, so a negative one cannot wrap.
struct TimeBound {
    std::uint64_t microseconds = 0;

    // A time bound written in microseconds, as the YAML and Excel loaders read
    // one, decided by the kernel (`aletheia_parse_time_bound`): its whole
    // microseconds, or the kernel's refusal typed as `Rational::from_decimal`'s.
    // The GHC runtime must be up.
    [[nodiscard]] static auto parse(std::string_view text) -> Result<TimeBound>;

    constexpr auto operator==(TimeBound const&) const -> bool = default;
};

// ---------------------------------------------------------------------------
// DLC: 0-15 (CAN-FD), validated at construction
// ---------------------------------------------------------------------------

class Dlc {
    std::uint8_t value_;
    explicit constexpr Dlc(std::uint8_t v) : value_(v) {}

public:
    [[nodiscard]] static constexpr auto create(std::uint8_t v) -> Result<Dlc> {
        if (v > 15)
            return detail::validation_refusal("DLC must be 0-15");
        return Dlc{v};
    }
    [[nodiscard]] constexpr auto value() const -> std::uint8_t { return value_; }
    auto operator<=>(Dlc const&) const = default;
};

namespace detail {
// CAN-FD DLC to payload byte count mapping (ISO 11898-1:2015 §8.4.2.4).
// DLC 0-8 maps directly; 9→12, 10→16, 11→20, 12→24, 13→32, 14→48, 15→64.
// One table, read forwards by dlc_to_bytes and backwards by bytes_to_dlc.
inline constexpr std::array<std::size_t, 16> k_dlc_bytes = {0, 1,  2,  3,  4,  5,  6,  7,
                                                            8, 12, 16, 20, 24, 32, 48, 64};
} // namespace detail

[[nodiscard]] constexpr auto dlc_to_bytes(Dlc dlc) -> std::size_t {
    return detail::k_dlc_bytes.at(dlc.value());
}

// Payload byte count to DLC code: the inverse of dlc_to_bytes over the same
// table, or an error for a byte count no DLC code denotes.  The search is the
// table's own, so the codes it can return are exactly the ones it holds; the
// factory's answer is returned as it is, so a code outside the table would be
// its error, read by every caller, and not an assertion inside a dereference.
[[nodiscard]] inline auto bytes_to_dlc(std::size_t byte_count) -> Result<Dlc> {
    auto const* const found = std::ranges::find(detail::k_dlc_bytes, byte_count);
    if (found == detail::k_dlc_bytes.end())
        return detail::validation_refusal("invalid DLC byte count: " + std::to_string(byte_count));
    return Dlc::create(static_cast<std::uint8_t>(found - detail::k_dlc_bytes.begin()));
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
    // shape.
    std::optional<bool> brs;
    // CAN-FD Error State Indicator (ISO 11898-1:2015 §10.4.3); same
    // semantics + pass-through status as brs.
    std::optional<bool> esi;
};

} // namespace aletheia

// `std::format("{}", key)` prints a SignMagnitude as its signed decimal, a
// zero unsigned.
template<>
struct std::formatter<aletheia::SignMagnitude> {
    static constexpr auto parse(std::format_parse_context& ctx)
        -> std::format_parse_context::iterator {
        return ctx.begin();
    }
    static auto format(aletheia::SignMagnitude const& v, std::format_context& ctx)
        -> std::format_context::iterator {
        return std::format_to(ctx.out(), "{}{}", v.negative && v.magnitude != 0 ? "-" : "",
                              v.magnitude);
    }
};
