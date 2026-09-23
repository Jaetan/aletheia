#!/usr/bin/env bash
# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
#
# Probes docs/development/BENCHMARKS.md.
# Claim: the compare.py command the Local baselines section prints runs as
# written over a fresh file beside its baseline and prints the per-lane table
# against the baseline the section describes. The fresh file is a copy of the
# committed baseline in a scratch directory, the command's results directory
# swapped for that one, so the probe measures nothing and needs no run.
# Non-zero exit: the section prints no such command, it fails, or its output
# has no table against the baseline.
set -u
cd "$(dirname "$0")/.." || exit 2
py=python/.venv/bin/python
[ -x "$py" ] || exit 2
dir=$(mktemp -d) || exit 2
trap 'rm -rf "$dir"' EXIT
cmd=$(sed -n '/^## Local baselines/,/^## /p' docs/development/BENCHMARKS.md | grep -m1 -E '^python/.venv/bin/python benchmarks/compare.py ')
[ -n "$cmd" ] || { echo "the section prints no compare.py command"; exit 1; }
# The command as printed names one binding's files by a glob over the results
# directory; the probe gives it a copy of that binding's baseline as the
# fresh file, in the scratch directory.
glob=${cmd##* }
lang=$(basename "$glob" | sed 's/_.*//')
mode=$(basename "$glob" | sed "s/^${lang}_//; s/\*.*//; s/\.json//")
base="benchmarks/results/${lang}_${mode}_baseline.json"
[ -f "$base" ] || { echo "the command names $glob, and $base does not exist"; exit 1; }
cp "$base" "$dir/" && cp "$base" "$dir/${lang}_${mode}.json" || exit 2
swapped=${cmd//benchmarks\/results\//$dir/}
case "$swapped" in
    "python/.venv/bin/python benchmarks/compare.py "*) ;;
    *) echo "not the command this probe runs: $swapped"; exit 1 ;;
esac
out=$(eval "$swapped" 2>&1) || { echo "the printed command failed"; echo "$out" | tail -5; exit 1; }
grep -q "$lang $mode against its baseline" <<< "$out" || { echo "no table against the baseline in the output"; echo "$out" | head -20; exit 1; }
echo "PASS: '$cmd' runs and prints the table against the baseline"
