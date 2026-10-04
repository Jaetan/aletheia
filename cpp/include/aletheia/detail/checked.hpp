// SPDX-FileCopyrightText: 2025 Nicolas Pelletier
// SPDX-License-Identifier: BSD-2-Clause
#pragma once

// Internal checked reads of a state a check has just ruled out. Reading the
// error of an expected that holds a value, a slice past the end of a span, or
// the text of a null C string is undefined; each read here throws instead, so
// a check that stops firing ends in an exception a test reports on every build
// rather than in a read of memory the program does not own. The library reads
// an optional's or an expected's value with `value()`, subscripts with `at()`
// and narrows a string view with `substr()`, the standard library's own
// checked forms; these cover what C++23 leaves unchecked.
//
// Each template only forwards to a check compiled once, so the check is one
// function however many types the library reads through it.

#include <cstddef>
#include <expected>
#include <span>
#include <string_view>

namespace aletheia::detail {

// Throws std::logic_error when `holds_value`.
void require_error(bool holds_value);

// Throws std::out_of_range when `count` elements from `offset` pass the end of
// `size` elements.
void require_within(std::size_t size, std::size_t offset, std::size_t count);

// The text the C string `text` holds; std::logic_error when it is null.
[[nodiscard]] auto c_string_view(const char* text) -> std::string_view;

// The error `result` holds; std::logic_error when it holds a value.
template<typename T, typename E>
[[nodiscard]] auto error_of(const std::expected<T, E>& result) -> const E& {
    require_error(result.has_value());
    return result.error();
}

// The `count` elements of `span` from `offset`; std::out_of_range when they
// pass its end.
template<typename T, std::size_t Extent>
[[nodiscard]] auto subspan_at(std::span<T, Extent> span, std::size_t offset, std::size_t count)
    -> std::span<T> {
    require_within(span.size(), offset, count);
    return span.subspan(offset, count);
}

// The elements of `span` from `offset` on; std::out_of_range when `offset`
// passes its end.
template<typename T, std::size_t Extent>
[[nodiscard]] auto subspan_at(std::span<T, Extent> span, std::size_t offset) -> std::span<T> {
    require_within(span.size(), offset, 0);
    return span.subspan(offset);
}

} // namespace aletheia::detail
