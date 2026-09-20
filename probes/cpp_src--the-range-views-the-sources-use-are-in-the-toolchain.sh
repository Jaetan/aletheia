#!/usr/bin/env bash
# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
#
# Probes the C++ sources under cpp/src and cpp/include.
# Claim: every range view those sources use is provided by the standard
# library the project's compiler compiles against, so a traversal written as
# a view compiles wherever the build runs and not only on the developer's
# machine, whose standard library is newer than the one CI installs. The set
# of views is read off the sources, so a view the sources take up is one this
# probe does not yet know, and that is a failure rather than a pass.
# Non-zero exit: a view the sources use is missing from the table below, its
# feature macro is missing or too old, or a use of it does not compile.
# Exits 0 with a note when the pinned compiler is absent, since the claim is
# about that compiler and is untestable without it.
set -u
cd "$(dirname "$0")/.." || exit 2
cxx=clang++-23
command -v "$cxx" > /dev/null || { echo "$cxx not installed, claim untestable"; exit 0; }

# view  feature macro  minimum value  (the C++20 views share the ranges macro)
table='
all        __cpp_lib_ranges            201911L
chunk      __cpp_lib_ranges_chunk      202202L
enumerate  __cpp_lib_ranges_enumerate  202302L
filter     __cpp_lib_ranges            201911L
iota       __cpp_lib_ranges            201911L
repeat     __cpp_lib_ranges_repeat     202207L
reverse    __cpp_lib_ranges            201911L
slide      __cpp_lib_ranges_slide      202202L
transform  __cpp_lib_ranges            201911L
zip        __cpp_lib_ranges_zip        202110L
'

views=$(git grep -ohE 'views::[a-z_]+' -- cpp/src cpp/include | sed 's/views:://' | sort -u) || exit 2
[ -n "$views" ] || { echo "no range view found under cpp/src or cpp/include; the scan is broken"; exit 2; }
status=0
asserts=''
for view in $views; do
    row=$(printf '%s\n' "$table" | awk -v v="$view" '$1 == v')
    [ -n "$row" ] || {
        echo "cpp/src or cpp/include uses views::$view, which this probe does not know"
        status=1
        continue
    }
    macro=$(printf '%s' "$row" | awk '{print $2}')
    least=$(printf '%s' "$row" | awk '{print $3}')
    asserts="$asserts
static_assert($macro >= $least, \"views::$view missing\");"
done
[ "$status" -eq 0 ] || exit 1

src=$(mktemp -t aletheia-views-XXXXXX.cpp) || exit 2
trap 'rm -f "$src"' EXIT
cat > "$src" <<CPP
#include <array>
#include <cstddef>
#include <cstdint>
#include <ranges>
#include <string_view>
#include <version>
$asserts

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
    for (auto const window : a | std::views::slide(2))
        n += static_cast<std::size_t>(window[0] + window[1]);
    for (auto const i : std::views::iota(std::uint32_t{1}, std::uint32_t{4}))
        n += i;
    for (auto const one : std::views::repeat(1, 3))
        n += static_cast<std::size_t>(one);
    for (auto const x : a | std::views::reverse | std::views::filter([](int v) { return v > 1; })
                            | std::views::transform([](int v) { return v * 2; }))
        n += static_cast<std::size_t>(x);
    for (auto const x : std::views::all(b))
        n += static_cast<std::size_t>(x);
    return n;
}
CPP

if ! "$cxx" -std=c++23 -fsyntax-only "$src" 2>&1; then
    echo "a range view the sources use does not compile under $cxx"
    exit 1
fi
echo "PASS: every range view cpp/src and cpp/include use is in the toolchain"
