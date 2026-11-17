// SPDX-FileCopyrightText: 2025 Nicolas Pelletier
// SPDX-License-Identifier: BSD-2-Clause
//
// The JSON value every request and reply crosses the boundary as, with every
// whole number exact to the kernel's 128 bits, and the reader and writer of
// its text.

#pragma once

#include <aletheia/types.hpp>

#include <nlohmann/json.hpp>

#include <map>
#include <optional>
#include <string>
#include <string_view>
#include <vector>

namespace aletheia::detail {

// A whole number is held exactly while its magnitude is at most 2^128-1: a
// non-negative one unsigned, a negative one down to -2^127 signed, and a
// negative one past it, which no 128-bit signed integer holds, as a binary node
// carrying its magnitude's 16 little-endian bytes under subtype 1. JSON text
// never yields a binary node, so the node denotes nothing else.
using Json = nlohmann::basic_json<std::map, std::vector, std::string, bool, __int128,
                                  unsigned __int128, double>;

// `input` read as JSON, each whole number held as `Json` says and any wider
// one, like any number with a fraction or an exponent, as a double. Malformed
// text throws nlohmann's parse_error. A value nested deeper than
// `max_nesting_depth` throws std::runtime_error ("JSON nesting depth N exceeds
// limit M"), which the response parsers answer as a Protocol error: a reply
// within the FFI's size cap can still nest deep enough to exhaust the stack
// of a recursive reader (AGENTS.md, "Adversarial-input bounds at parser
// surfaces"), and the depth is a guard on the kernel's replies rather than one
// of the kernel's own input bounds, so it carries no `bound_kind`.
[[nodiscard]] auto parse_json(std::string_view input) -> Json;

// `j` as `Json::dump(indent)` writes it, compact for a negative `indent`, with
// a binary node written as `-` and its magnitude's digits. A string that is
// not UTF-8 throws nlohmann's type_error, as `dump` does.
[[nodiscard]] auto dump_json(Json const& j, int indent = -1) -> std::string;

// A non-negative whole number's value, or nullopt for any other node.
[[nodiscard]] auto uint128_of(Json const& j) -> std::optional<unsigned __int128>;

// A whole number's sign and magnitude, or nullopt for any other node.
[[nodiscard]] auto sign_magnitude_of(Json const& j) -> std::optional<SignMagnitude>;

// The node a whole number is held in; a zero is written unsigned.
[[nodiscard]] auto json_of(bool negative, unsigned __int128 magnitude) -> Json;
[[nodiscard]] auto json_of(SignMagnitude value) -> Json;

} // namespace aletheia::detail
