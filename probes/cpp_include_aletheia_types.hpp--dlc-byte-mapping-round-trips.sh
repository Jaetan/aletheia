#!/usr/bin/env bash
# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
#
# Probes cpp/include/aletheia/types.hpp.
# Claim: dlc_to_bytes maps the sixteen DLC codes to the CAN-FD byte counts
# 0-8, 12, 16, 20, 24, 32, 48, 64, bytes_to_dlc inverts it for every code,
# and refuses every byte count from 0 to 64 that no code denotes. Non-zero
# exit: any code or count disagrees.
set -u
cd "$(dirname "$0")/.." || exit 2
scratch=cpp/build/probe-scratch/types-dlc
mkdir -p "$scratch" || exit 2
cat > "$scratch/t.cpp" <<'CPP'
#include <aletheia/types.hpp>
#include <array>
#include <cstdio>
using namespace aletheia;
int main() {
    constexpr std::array<std::size_t, 16> expected{0, 1, 2, 3, 4, 5, 6, 7, 8, 12, 16, 20, 24, 32, 48, 64};
    int failures = 0;
    for (std::uint8_t code = 0; code < 16; ++code) {
        const auto dlc = Dlc::create(code).value();
        if (dlc_to_bytes(dlc) != expected[code]) ++failures;
        const auto back = bytes_to_dlc(expected[code]);
        if (!back || back->value() != code) ++failures;
    }
    for (std::size_t n = 0; n <= 64; ++n) {
        bool valid = false;
        for (auto e : expected) valid = valid || e == n;
        if (bytes_to_dlc(n).has_value() != valid) ++failures;
    }
    if (bytes_to_dlc(65).has_value()) ++failures;
    std::printf("failures=%d\n", failures);
    return failures == 0 ? 0 : 1;
}
CPP
clang++-22 -std=c++23 -Icpp/include "$scratch/t.cpp" -o "$scratch/t" > "$scratch/compile.log" 2>&1 || { tail -5 "$scratch/compile.log"; exit 1; }
"$scratch/t"
