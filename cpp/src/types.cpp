// SPDX-FileCopyrightText: 2025 Nicolas Pelletier
// SPDX-License-Identifier: BSD-2-Clause
// Rational::from_decimal — parses a decimal literal into an exact Rational via
// the Agda kernel's decimal SSOT (the float principle: a decimal is an exact
// rational, never a float). Thin delegate: fetch the raw wire envelope from the
// renderer's `parse_decimal_ffi` (lazy-load + vocal RTS gate) and decode it with
// the shared wire decoder `decode_decimal_response`.
#include <aletheia/types.hpp>

#include <aletheia/detail/rational_renderer.hpp>

#include "detail/json.hpp"

#include <string_view>

namespace aletheia {

auto Rational::from_decimal(std::string_view s) -> Rational {
    return detail::decode_decimal_response(detail::parse_decimal_ffi(s));
}

} // namespace aletheia
