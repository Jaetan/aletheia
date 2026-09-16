#!/usr/bin/env bash
# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
#
# Probes cpp/.clang-tidy.
# Claim: the file disables llvm-header-guard and portability-avoid-pragma-once
# because every header under cpp/include and cpp/src uses #pragma once, so no
# check enforces a guard. Non-zero exit: a tracked header has no #pragma once.
set -u
cd "$(dirname "$0")/.." || exit 2
status=0
for h in $(git ls-files 'cpp/include/*.hpp' 'cpp/src/*.hpp'); do
    grep -q '^#pragma once' "$h" || { echo "no #pragma once: $h"; status=1; }
done
exit $status
