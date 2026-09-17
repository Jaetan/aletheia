#!/usr/bin/env bash
# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
#
# Probes cpp/.clang-tidy.
# Claim: readability-implicit-bool-conversion flags `if (ptr)` and `if (n)`
# with no options set, so AllowIntegerConditions and AllowPointerConditions
# default to false and setting them to false restates the default.
# Non-zero exit: either condition goes undiagnosed under the defaults.
set -u
cd "$(dirname "$0")/.." || exit 2
scratch=cpp/build/probe-scratch/implicit-bool
mkdir -p "$scratch" || exit 2
cat > "$scratch/t.cpp" <<'CPP'
int k(int* p, int n) {
    if (p) { return 1; }
    if (n) { return 2; }
    return 0;
}
CPP
out=$(clang-tidy-23 --quiet -checks='-*,readability-implicit-bool-conversion' \
    -config='{}' "$scratch/t.cpp" -- -std=c++23 2>/dev/null)
printf '%s\n' "$out" | grep -q 't.cpp:2:' && printf '%s\n' "$out" | grep -q 't.cpp:3:'
