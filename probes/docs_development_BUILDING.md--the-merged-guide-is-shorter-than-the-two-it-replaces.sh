#!/usr/bin/env bash
# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
#
# Probes docs/development/BUILDING.md.
# Claim: the guide, which now carries the dependency and licence ledger, is
# shorter than the two documents it replaced were together: the guide alone
# measured 4195 words and the dependency document it absorbed 1095 (wc -w),
# 5290 in all, on the tree before the merge. A pass that grows the merged
# guide past that is a
# pass that wrote more than the two documents it was meant to compress.
# Non-zero exit: the guide is at or past 5290 words.
set -u
cd "$(dirname "$0")/.." || exit 2
doc=docs/development/BUILDING.md
[ -f "$doc" ] || exit 2
ceiling=5290
words=$(wc -w < "$doc")
[ "$words" -lt "$ceiling" ] || { echo "$doc is $words words, not under the $ceiling the two documents measured"; exit 1; }
echo "PASS: $doc is $words words, under $ceiling"
