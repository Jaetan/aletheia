#!/usr/bin/env bash
# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
#
# Probes benchmarks/compare.py.
# Claim: given result files of several modes at once, the comparison prints a
# table for every mode it was given. Files used to be keyed on their language
# alone, so of one binding's throughput, latency and scaling files only the
# last one read survived, and the other two modes vanished from the output
# while the run reported success.
# Non-zero exit: a mode among the files given has no table in the output.
set -u
cd "$(dirname "$0")/.." || exit 2
py=python/.venv/bin/python
[ -x "$py" ] || exit 2
out=$("$py" benchmarks/compare.py benchmarks/results/*_baseline.json 2>&1) || { echo "compare.py failed"; echo "$out" | tail -5; exit 1; }
status=0
for title in "Throughput Comparison" "Latency Comparison" "Scaling Comparison"; do
    grep -q "$title" <<< "$out" || { echo "no table for: $title"; status=1; }
done
exit $status
