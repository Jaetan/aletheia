// SPDX-FileCopyrightText: 2025 Nicolas Pelletier
// SPDX-License-Identifier: BSD-2-Clause

#include <aletheia/detail/checked.hpp>

#include <cstddef>
#include <format>
#include <stdexcept>
#include <string_view>

namespace aletheia::detail {

void require_error(bool holds_value) {
    if (holds_value)
        throw std::logic_error("read the error of an expected that holds a value");
}

void require_within(std::size_t size, std::size_t offset, std::size_t count) {
    if (offset > size || count > size - offset)
        throw std::out_of_range(
            std::format("{} elements at {} pass the end of a span of {}", count, offset, size));
}

auto c_string_view(const char* text) -> std::string_view {
    if (text == nullptr)
        throw std::logic_error("read the text of a null C string");
    return text;
}

} // namespace aletheia::detail
