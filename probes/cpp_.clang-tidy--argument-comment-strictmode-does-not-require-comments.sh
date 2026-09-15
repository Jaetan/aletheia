#!/usr/bin/env bash
# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
#
# Probes cpp/.clang-tidy.
# Claim: bugprone-argument-comment.StrictMode does not require /*name=*/
# comments on positional arguments; it only makes an argument comment that is
# present match the parameter name exactly. Non-zero exit: a call with no
# argument comments is diagnosed under StrictMode (the comment in the file
# would then be right and this probe wrong), or a comment naming the wrong
# parameter is not diagnosed.
set -u
cd "$(dirname "$0")/.." || exit 2
scratch=cpp/build/probe-scratch/argument-comment
mkdir -p "$scratch" || exit 2
cat > "$scratch/t.cpp" <<'CPP'
void f(int alpha, int beta);
void g() {
    f(1, 2);
    f(/*beta=*/1, 2);
}
CPP
out=$(clang-tidy-22 --quiet -checks='-*,bugprone-argument-comment' \
    -config='{CheckOptions: {bugprone-argument-comment.StrictMode: "true"}}' \
    "$scratch/t.cpp" -- -std=c++23 2>/dev/null)
uncommented=$(printf '%s\n' "$out" | grep -c 't.cpp:3:')
mismatched=$(printf '%s\n' "$out" | grep -c 't.cpp:4:')
[ "$uncommented" -eq 0 ] && [ "$mismatched" -ge 1 ]
