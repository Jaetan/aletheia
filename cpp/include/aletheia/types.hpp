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
#include <limits>
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
// factory.  Class (not struct): a public-fields
// struct invites direct writes that would bypass the invariant; private
// fields + `numerator()` / `denominator()` accessors make `den_ > 0` a
// type-level guarantee rather than a callsite discipline.
class Rational {
public:
    constexpr Rational() = default;

    // Exact-numeric boundary — the float principle: a `double` must not narrow
    // silently into the numerator/denominator, and a `bool` must not pass as a
    // numeric value.  A non-template `Rational(int64_t, int64_t)` admits both
    // through paren-init (`Rational(7.9, 2)` truncates to 7/2 with only a
    // warning; `Rational(true, 1)` is silent), so the parameters are constrained
    // to non-bool integral types — a decimal must instead go through
    // `Rational::from_decimal` (the kernel decimal SSOT).  Go/Rust get this for
    // free from their `int64`-typed rationals; this brings C++ to the same bar.
    // Constant expressions only: `make` checks the pair, so a literal outside
    // int64 or with a denominator that is not positive fails the build, and a
    // pair known at run time goes through `make` or `integer`.
    template<std::integral N, std::integral D>
        requires(!std::same_as<N, bool> && !std::same_as<D, bool>)
    consteval Rational(N n, D d) : Rational(make(n, d).value()) {}

    [[nodiscard]] constexpr auto numerator() const -> std::int64_t { return num_; }

private:
    // The stores, reached once the pair is known to hold the invariant.
    struct Unchecked {};
    constexpr Rational(std::int64_t n, std::int64_t d, Unchecked /*unchecked*/)
        : num_(n)
        , den_(d) {}

public:
    [[nodiscard]] constexpr auto denominator() const -> std::int64_t { return den_; }

    // Cross-multiply comparison (avoids floating-point).
    // __int128 is a Clang/GCC extension (not standard C++); the project
    // builds Clang-only on Linux (latest stable Clang — see
    // cpp/CMakeLists.txt), where it is always available.
    // A double-precision fallback would silently lose precision on large
    // numerator/denominator pairs, so we refuse to build rather than ship it.
    static_assert(sizeof(__int128) >= 16, "Aletheia requires __int128 support "
                                          "(Clang on Linux — see cpp/CMakeLists.txt).");
    constexpr auto operator<=>(const Rational& rhs) const {
        // a/b <=> c/d  iff  a*d <=> c*b  (denominators always positive)
        auto const lhs_prod = static_cast<__int128>(num_) * rhs.den_;
        auto const rhs_prod = static_cast<__int128>(rhs.num_) * den_;
        return lhs_prod <=> rhs_prod;
    }
    constexpr auto operator==(const Rational& rhs) const -> bool {
        return (*this <=> rhs) == std::strong_ordering::equal;
    }

    // Validated factory: a Validation error for a component outside int64 or a
    // denominator that is not positive.
    template<std::integral N, std::integral D>
        requires(!std::same_as<N, bool> && !std::same_as<D, bool>)
    [[nodiscard]] static constexpr auto make(N num, D den) -> Result<Rational> {
        // Representability before narrowing: a uint64_t > INT64_MAX would
        // otherwise wrap to a negative/wrong value before the den > 0 check,
        // yielding a misleading error or an incorrect Rational.
        if (!std::in_range<std::int64_t>(num) || !std::in_range<std::int64_t>(den))
            return detail::validation_refusal("Rational: numerator/denominator out of int64 range");
        auto const den64 = static_cast<std::int64_t>(den);
        if (den64 <= 0)
            return detail::validation_refusal("Rational denominator must be positive");
        return Rational{static_cast<std::int64_t>(num), den64, Unchecked{}};
    }

    // The whole number `n / 1`, which cannot fail: the type holds every value
    // of `n` within int64, so a `uint64_t`, like a `bool` or a `double`, does
    // not compile.
    template<std::integral I>
        requires(!std::same_as<I, bool> &&
                 std::in_range<std::int64_t>(std::numeric_limits<I>::min()) &&
                 std::in_range<std::int64_t>(std::numeric_limits<I>::max()))
    [[nodiscard]] static constexpr auto integer(I n) -> Rational {
        return Rational{static_cast<std::int64_t>(n), 1, Unchecked{}};
    }

    // Parse a decimal literal into an exact Rational via the Agda kernel's
    // decimal SSOT (`aletheia_parse_decimal`) — the float principle: a decimal
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
    requires { typename std::integral_constant<std::int64_t, Rational{N, D}.numerator()>; };
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
                  detail::RationalIntegerable<std::uint32_t>,
              "a whole number of any type within int64 must build");
static_assert(!detail::RationalIntegerable<std::uint64_t>,
              "a type passing int64 must not build a whole number");
static_assert(!detail::RationalIntegerable<double>, "a double must not narrow via integer");
static_assert(!detail::RationalIntegerable<bool>, "a bool must not pass through integer");
static_assert(detail::RationalLiteral<1, 10>, "a literal fraction must build");
static_assert(!detail::RationalLiteral<1, 0>, "a zero denominator must not build");
static_assert(!detail::RationalLiteral<1, -1>, "a negative denominator must not build");
static_assert(!detail::RationalLiteral<std::uint64_t{1} << 63U, 1>,
              "a numerator past int64 must not build");
static_assert(!detail::RationalLiteral<1, std::uint64_t{1} << 63U>,
              "a denominator past int64 must not build");

// ---------------------------------------------------------------------------
// Integer domain types (distinct bit-level types)
// ---------------------------------------------------------------------------

using BitPosition = Strong<struct BitPositionTag, std::uint16_t>;
using BitLength = Strong<struct BitLengthTag, std::uint16_t>;
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
    [[nodiscard]] static constexpr auto create(std::uint16_t v) -> Result<StandardId> {
        if (v > max_id)
            return detail::validation_refusal("Standard CAN ID must be 0-2047");
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
    [[nodiscard]] static constexpr auto create(std::uint32_t v) -> Result<ExtendedId> {
        if (v > max_id)
            return detail::validation_refusal("Extended CAN ID must be 0-536870911");
        return ExtendedId{v};
    }
    [[nodiscard]] constexpr auto value() const -> std::uint32_t { return value_; }
    auto operator<=>(const ExtendedId&) const = default;
};

using CanId = std::variant<StandardId, ExtendedId>;

/// Extract the underlying 11- or 29-bit value from a CanId, regardless
/// of standard vs extended discrimination, so call sites need not visit
/// the variant themselves.
[[nodiscard]] constexpr auto can_id_value(const CanId& id) -> std::uint32_t {
    return std::visit([](auto const& v) -> std::uint32_t { return v.value(); }, id);
}

/// Returns true when the CanId carries an `ExtendedId` (29-bit) variant,
/// false for `StandardId` (11-bit).
[[nodiscard]] constexpr auto can_id_is_extended(const CanId& id) -> bool {
    return std::holds_alternative<ExtendedId>(id);
}

// ---------------------------------------------------------------------------
// Timestamp: microseconds since trace start (chrono, not bare integer)
// ---------------------------------------------------------------------------

using Timestamp = std::chrono::microseconds;

// Scale into the Timestamp domain: the check builder's millisecond bound and
// the renderer's time bound (Go `usPerMillisecond`, Rust `US_PER_MILLISECOND`).
inline constexpr Timestamp::rep us_per_millisecond = 1'000;
inline constexpr Timestamp::rep us_per_second = 1'000'000;

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
    auto operator<=>(const Dlc&) const = default;
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
