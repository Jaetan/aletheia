// SPDX-FileCopyrightText: 2025 Nicolas Pelletier
// SPDX-License-Identifier: BSD-2-Clause
#pragma once

// The value a setup step's Result holds, read in a test: the test fails with
// the error's text where the step refused, so a refused backend or client
// reads as its refusal rather than as std::bad_expected_access.

#include <aletheia/detail/checked.hpp>
#include <aletheia/error.hpp>

#include <catch2/catch_test_macros.hpp>

#include <utility>

namespace aletheia::test {

template<typename T>
[[nodiscard]] auto required(Result<T> result) -> T {
    if (!result)
        FAIL(detail::error_of(result).text());
    return std::move(result).value();
}

} // namespace aletheia::test
