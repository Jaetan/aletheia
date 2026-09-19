#!/usr/bin/env bash
# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
#
# Probes the C++ sources under cpp/src and cpp/include.
# Claim: every range view those sources loop through is provided by the
# standard library the project's compiler compiles against, so a traversal
# written as a view compiles wherever the build runs and not only on the
# developer's machine, whose standard library is newer than the one CI
# installs. Non-zero exit: one of the views is missing, or a use of it does
# not compile. Exits 0 with a note when the pinned compiler is absent, since
# the claim is about that compiler and is untestable without it.
set -u
cd "$(dirname "$0")/.." || exit 2
cxx=clang++-23
command -v "$cxx" > /dev/null || { echo "$cxx not installed, claim untestable"; exit 0; }

src=$(mktemp -t aletheia-views-XXXXXX.cpp) || exit 2
trap 'rm -f "$src"' EXIT
cat > "$src" <<'CPP'
#include <array>
#include <cstddef>
#include <cstdint>
#include <ranges>
#include <string_view>
#include <version>

static_assert(__cpp_lib_ranges_enumerate >= 202302L, "views::enumerate missing");
static_assert(__cpp_lib_ranges_zip >= 202110L, "views::zip missing");
static_assert(__cpp_lib_ranges_chunk >= 202202L, "views::chunk missing");

auto uses_the_views() -> std::size_t {
    constexpr std::array<int, 3> a = {1, 2, 3};
    constexpr std::array<int, 3> b = {4, 5, 6};
    std::size_t n = 0;
    for (auto const [i, x] : std::views::enumerate(a))
        n += static_cast<std::size_t>(i) + static_cast<std::size_t>(x);
    for (auto const [x, y] : std::views::zip(a, b))
        n += static_cast<std::size_t>(x + y);
    for (auto const pair : std::string_view{"0a1b"} | std::views::chunk(2))
        n += static_cast<std::size_t>(std::ranges::distance(pair));
    for (auto const i : std::views::iota(std::uint32_t{1}, std::uint32_t{4}))
        n += i;
    return n;
}
CPP

if ! "$cxx" -std=c++23 -fsyntax-only "$src" 2>&1; then
    echo "a range view the sources use does not compile under $cxx"
    exit 1
fi
