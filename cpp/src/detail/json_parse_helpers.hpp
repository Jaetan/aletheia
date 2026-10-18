// SPDX-FileCopyrightText: 2025 Nicolas Pelletier
// SPDX-License-Identifier: BSD-2-Clause
// What the JSON response parsers and the DBC parsers share: the table lookup,
// the integer reads that refuse a float or an out-of-range value, and the
// rational and DBC decoders each side defines for the other.
#pragma once

#include <aletheia/dbc.hpp>
#include <aletheia/types.hpp>

#include <nlohmann/json.hpp>

#include <cstdint>
#include <limits>
#include <optional>
#include <stdexcept>
#include <string>
#include <string_view>
#include <type_traits>
#include <utility>

namespace aletheia {

// The value of a table entry, or nullopt when the table has no such entry.
// Every string-to-enum table the JSON parsers keep is an array scanned
// linearly, which is fine on these cold paths.
template<typename Table>
auto lookup(const Table& table, std::string_view wire)
    -> std::optional<typename Table::value_type::second_type> {
    for (auto const& [name, value] : table)
        if (name == wire)
            return value;
    return std::nullopt;
}

} // namespace aletheia

namespace aletheia::detail {

using Json = nlohmann::json;

// Reject a JSON float in an integer-only wire position.  nlohmann silently
// `static_cast`s a JSON float to an integer type on `get<intT>()` (e.g.
// 5.9 → 5), corrupting the value *before* any range check runs.  The FFI wire
// and DBC integer-position fields are integer-only by construction — the Agda
// core never emits a float there — so a non-integer number is a wire-format
// violation and is rejected here rather than silently truncated.  Exact
// rationals travel as `{numerator, denominator}` objects, never as floats.
//
// `require_int` accepts negatives (signed positions); `require_uint` rejects
// negatives as well as floats (`is_number_unsigned` is false for both).  Both
// preserve the caller's existing range check, which still runs on the returned
// integer.
//
// Both also refuse a value the position cannot hold.  The JSON library keeps
// a positive literal above the signed maximum as an unsigned one, and the
// narrowing conversion wraps it: without this check an index one past the
// signed 64-bit maximum reads as the most negative one and the caller's sign
// test calls it negative, a CAN id of 2^32 reads as a valid zero, a frame
// byte of 256 reads as zero.  The refusal names the position's own range, as
// the kernel names the bound it refuses at its own entry.
template<typename T>
auto out_of_range(const Json& j, std::string_view context) -> std::runtime_error {
    return std::runtime_error(std::string{context} + " is out of range (" +
                              std::to_string(std::numeric_limits<T>::min()) + " to " +
                              std::to_string(std::numeric_limits<T>::max()) +
                              "), got: " + j.dump());
}

template<typename T>
auto require_int(const Json& j, std::string_view context) -> T {
    if (!j.is_number_integer())
        throw std::runtime_error(std::string{context} + " must be an integer, got: " + j.dump());
    // A signed value always fits a 64-bit target, so that branch is a check
    // only for narrower targets.
    bool fits = true;
    if (j.is_number_unsigned())
        fits = std::in_range<T>(j.get<std::uint64_t>());
    else if constexpr (!std::is_same_v<T, std::int64_t>)
        fits = std::in_range<T>(j.get<std::int64_t>());
    if (!fits)
        throw out_of_range<T>(j, context);
    return j.get<T>();
}

template<typename T>
auto require_uint(const Json& j, std::string_view context) -> T {
    if (!j.is_number_unsigned())
        throw std::runtime_error(std::string{context} +
                                 " must be a non-negative integer, got: " + j.dump());
    auto const wide = j.get<std::uint64_t>();
    // A 64-bit unsigned target holds every value the reader can produce, so
    // the range check exists only for the narrower ones.
    if constexpr (std::numeric_limits<T>::max() < std::numeric_limits<std::uint64_t>::max()) {
        if (!std::in_range<T>(wide))
            throw out_of_range<T>(j, context);
    }
    return static_cast<T>(wide);
}

auto parse_rational(const Json& j) -> Rational;
auto parse_dbc_definition(const Json& j) -> DbcDefinition;

} // namespace aletheia::detail
