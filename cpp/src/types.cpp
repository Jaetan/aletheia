// SPDX-FileCopyrightText: 2025 Nicolas Pelletier
// SPDX-License-Identifier: BSD-2-Clause
// The out-of-line half of `Rational::from_decimal`, whose grammar, refusals and
// float principle are stated with the declaration in types.hpp. The kernel owns
// all three; this file only carries a refusal's wire envelope from the renderer
// to the decoder that reads it.
#include <aletheia/types.hpp>

#include <aletheia/detail/checked.hpp>
#include <aletheia/detail/rational_renderer.hpp>
#include <aletheia/error.hpp>

#include "detail/json.hpp"

#include <string_view>

namespace aletheia {

auto Rational::from_decimal(std::string_view s) -> Rational {
    auto answer = detail::parse_decimal_ffi(s);
    if (!answer)
        throw AletheiaException(detail::decimal_refusal(detail::error_of(answer)));
    return answer.value();
}

} // namespace aletheia
