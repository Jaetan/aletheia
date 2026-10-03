// SPDX-FileCopyrightText: 2025 Nicolas Pelletier
// SPDX-License-Identifier: BSD-2-Clause
//
// The rational renderer refuses, naming the build, when it finds no kernel
// library. A process of its own, because the renderer searches once per
// process and keeps the answer: a process that had found the library could not
// show the refusal.

#include <catch2/catch_test_macros.hpp>
#include <catch2/matchers/catch_matchers.hpp>
#include <catch2/matchers/catch_matchers_string.hpp>

#include <aletheia/detail/rational_renderer.hpp>
#include <aletheia/types.hpp>

#include <filesystem>

#include "temp_path.hpp"

TEST_CASE("the renderer refuses when it finds no library", "[rational_renderer]") {
    // Nothing names a library: the variable is cleared, no backend has
    // registered one, and the working directory is two levels inside this
    // process's own scratch directory, so every path the search tries from it
    // lies in a tree that holds no build.
    REQUIRE(::unsetenv("ALETHEIA_LIB") == 0);
    const aletheia::test::TempPath nest{aletheia::test::scratch_dir() / "outer" / "inner",
                                        aletheia::test::AsDirectory{}};
    std::filesystem::current_path(nest.path);

    auto const not_found = Catch::Matchers::ContainsSubstring("libaletheia-ffi.so not found");
    REQUIRE_THROWS_WITH(aletheia::detail::format_rational_ffi(1, 2), not_found);
    REQUIRE_THROWS_WITH(aletheia::Rational::from_decimal("1.5"), not_found);
}
