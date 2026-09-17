#!/usr/bin/env bash
# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
#
# Probes cpp/.clang-tidy.
# Claim: cppcoreguidelines-init-variables.IncludeStyle only picks the include
# style of the fix-it that adds <math.h> for a NAN initialiser; it neither
# silences nor changes the finding on an uninitialised fundamental variable.
# Non-zero exit: the diagnostics differ between IncludeStyle google and llvm.
set -u
cd "$(dirname "$0")/.." || exit 2
scratch=cpp/build/probe-scratch/init-variables
mkdir -p "$scratch" || exit 2
cat > "$scratch/t.cpp" <<'CPP'
int h() {
    int n;
    n = 1;
    return n;
}
CPP
run() {
    clang-tidy-23 --quiet -checks='-*,cppcoreguidelines-init-variables' \
        -config="{CheckOptions: {cppcoreguidelines-init-variables.IncludeStyle: $1}}" \
        "$scratch/t.cpp" -- -std=c++23 2>/dev/null | grep 'warning:'
}
google=$(run google); llvm=$(run llvm)
[ -n "$google" ] && [ "$google" = "$llvm" ]
