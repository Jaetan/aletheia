#!/usr/bin/env bash
# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
#
# Probes cpp/include/aletheia/types.hpp.
# Claim: Rational's three-way comparison orders exactly as the fractions it
# denotes, including pairs whose cross products exceed 64 bits (the
# __int128 path), and equal fractions with different representations compare
# equal. Checked against Python's Fraction over a fixed list of pairs that
# the C++ program prints its verdicts for. Non-zero exit: a verdict differs.
set -u
cd "$(dirname "$0")/.." || exit 2
scratch=cpp/build/probe-scratch/types-rational
mkdir -p "$scratch" || exit 2
cat > "$scratch/pairs.txt" <<'TXT'
1 2 2 4
1 3 1 2
-1 3 1 3
9223372036854775807 1 9223372036854775806 1
9223372036854775807 2 9223372036854775806 1
-9223372036854775807 3 -9223372036854775806 3
9223372036854775807 9223372036854775807 1 1
1 9223372036854775807 1 9223372036854775806
-5 7 -10 14
0 1 0 5
TXT
cat > "$scratch/t.cpp" <<'CPP'
#include <aletheia/types.hpp>
#include <cstdint>
#include <cstdio>
using namespace aletheia;
int main() {
    long long a, b, c, d;
    while (std::scanf("%lld %lld %lld %lld", &a, &b, &c, &d) == 4) {
        const Rational x{static_cast<std::int64_t>(a), static_cast<std::int64_t>(b)};
        const Rational y{static_cast<std::int64_t>(c), static_cast<std::int64_t>(d)};
        const auto o = x <=> y;
        std::printf("%s\n", o < 0 ? "lt" : o > 0 ? "gt" : "eq");
    }
}
CPP
clang++-23 -std=c++23 -Icpp/include "$scratch/t.cpp" -o "$scratch/t" > "$scratch/compile.log" 2>&1 || { tail -5 "$scratch/compile.log"; exit 1; }
"$scratch/t" < "$scratch/pairs.txt" > "$scratch/got.txt"
python/.venv/bin/python - "$scratch/pairs.txt" "$scratch/got.txt" <<'PY'
import sys
from fractions import Fraction
pairs = [tuple(map(int, l.split())) for l in open(sys.argv[1]) if l.strip()]
got = [l.strip() for l in open(sys.argv[2]) if l.strip()]
bad = 0
for (a, b, c, d), g in zip(pairs, got, strict=True):
    x, y = Fraction(a, b), Fraction(c, d)
    want = "lt" if x < y else "gt" if x > y else "eq"
    if want != g: print(f"{a}/{b} vs {c}/{d}: want {want} got {g}"); bad += 1
print(f"pairs {len(pairs)} bad {bad}")
sys.exit(1 if bad else 0)
PY
