#!/usr/bin/env bash
# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
#
# Claim: the file-to-gate lens is reproducible, so the two ends of a round can be diffed.
# Probes: .archive/reviews/frev-cpp-2026-09-15/lens/file_gate_map.py and the base row it produced.
# Non-zero means the recorded base map is not what the saved generator produces from the
# base tree, so the lens's own record cannot be reproduced and nothing can be diffed against it.
set -eu
root=$(git rev-parse --show-toplevel)
cd "$root"
lens=.archive/reviews/frev-cpp-2026-09-15/lens/file_gate_map.py
recorded=.archive/reviews/frev-cpp-2026-09-15/base/file_gate_map.tsv
base=726198bb
python=python/.venv/bin/python
[ -x "$python" ] || python=python3

tmp=$(mktemp)
trap 'rm -f "$tmp"' EXIT
"$python" "$lens" cpp/ "$base" > "$tmp" 2>/dev/null

if ! diff -q "$recorded" "$tmp" >/dev/null; then
    echo "FAIL: the saved generator does not reproduce the recorded base map"
    diff "$recorded" "$tmp" | head -20
    exit 1
fi
echo "PASS: the base map is reproduced from the base tree by the saved generator"
