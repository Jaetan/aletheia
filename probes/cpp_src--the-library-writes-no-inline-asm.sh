#!/usr/bin/env bash
# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
#
# Probes cpp/src and cpp/include.
# Claim: the library writes no inline assembly. The call mutators refuse an
# inline asm statement and the callbr instruction it lowers to, since
# branching past asm labels is not a call removal, and that refusal costs the
# sweep nothing only while the library writes none. Non-zero exit: a source
# or header under cpp/src or cpp/include carries an asm statement.
set -u
cd "$(dirname "$0")/.." || exit 2
hits=$(grep -rnE '(^|[^[:alnum:]_])(__asm__?|asm)[[:space:]]*(volatile[[:space:]]*)?\(' cpp/src cpp/include || true)
if [ -n "$hits" ]; then
    printf '%s\n' "$hits"
    echo "FAIL: the library writes inline assembly, which the call mutators refuse"
    exit 1
fi
echo "PASS: no inline assembly under cpp/src or cpp/include"
