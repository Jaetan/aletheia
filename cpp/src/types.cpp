// SPDX-FileCopyrightText: 2025 Nicolas Pelletier
// SPDX-License-Identifier: BSD-2-Clause
// The out-of-line half of `Rational::from_decimal`, whose grammar, refusals and
// float principle are stated with the declaration in types.hpp. The kernel owns
// all three; this file only carries the wire envelope from the renderer to the
// decoder that reads it.
#include <aletheia/types.hpp>

#include <aletheia/detail/rational_renderer.hpp>

#include "detail/json.hpp"

#include <string_view>

namespace aletheia {

auto Rational::from_decimal(std::string_view s) -> Rational {
    return detail::decode_decimal_response(detail::parse_decimal_ffi(s));
}

} // namespace aletheia
