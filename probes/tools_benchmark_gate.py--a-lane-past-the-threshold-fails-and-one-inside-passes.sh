#!/usr/bin/env bash
# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
#
# Probes tools/benchmark_gate.py.
# Claim: against a bar of 1000 frames a second and a threshold of 30%, a lane
# measured at 690 fails the gate and a lane measured at 710 passes it; the
# threshold is a strict bound on the slowdown, read from the flag.
# Non-zero exit: the slower lane passed or the faster lane failed. Exits 2 when
# the interpreter is missing or the scratch directory cannot be made.
set -u
cd "$(dirname "$0")/.." || exit 2
py=python/.venv/bin/python
[ -x "$py" ] || exit 2
mkdir -p tools/ci-output || exit 2
work=$(mktemp -d tools/ci-output/.benchmark-gate-XXXXXX) || exit 2
trap 'rm -rf "$work"' EXIT
mkdir -p "$work/slow" "$work/fast" || exit 2
lane='CAN 2.0B: Frame Building'
printf '{"cpp": {"%s": 1000.0}}\n' "$lane" > "$work/baseline.json"
printf '{"results": [{"name": "%s", "fps_mean": 690.0}]}\n' "$lane" > "$work/slow/cpp_throughput.json"
printf '{"results": [{"name": "%s", "fps_mean": 710.0}]}\n' "$lane" > "$work/fast/cpp_throughput.json"
"$py" -m tools.benchmark_gate --results-dir "$work/slow" --baseline "$work/baseline.json" --threshold-pct 30
slow=$?
"$py" -m tools.benchmark_gate --results-dir "$work/fast" --baseline "$work/baseline.json" --threshold-pct 30
fast=$?
echo "slow lane exit $slow, fast lane exit $fast"
[ "$slow" -eq 1 ] && [ "$fast" -eq 0 ]
