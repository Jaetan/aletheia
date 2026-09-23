#!/usr/bin/env bash
# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
#
# Probes tools/benchmark_gate.py.
# Claim: against a baseline naming two lanes for cpp, a run whose cpp result
# file carries one of them fails the gate and names the other on stderr, a run
# whose cpp result file carries no lane at all fails naming both, and a run
# with no cpp result file (the binding did not build) passes with the binding
# skipped.
# Non-zero exit: a present binding short of a lane passed, the missing lane
# was not named, or an absent binding failed. Exits 2 when the interpreter is
# missing or the scratch directory cannot be made.
set -u
cd "$(dirname "$0")/.." || exit 2
py=python/.venv/bin/python
[ -x "$py" ] || exit 2
mkdir -p tools/ci-output || exit 2
work=$(mktemp -d tools/ci-output/.benchmark-gate-XXXXXX) || exit 2
trap 'rm -rf "$work"' EXIT
mkdir -p "$work/short" "$work/empty" "$work/absent" || exit 2
lane='CAN 2.0B: Frame Building'
other='CAN 2.0B: Signal Extraction'
printf '{"cpp": {"%s": 1000.0, "%s": 1000.0}}\n' "$lane" "$other" > "$work/baseline.json"
printf '{"results": [{"name": "%s", "fps_mean": 1000.0}]}\n' "$lane" > "$work/short/cpp_throughput.json"
printf '{"results": []}\n' > "$work/empty/cpp_throughput.json"
printf '{"results": [{"name": "%s", "fps_mean": 1000.0}]}\n' "$lane" > "$work/absent/go_throughput.json"
"$py" -m tools.benchmark_gate --results-dir "$work/short" --baseline "$work/baseline.json" 2> "$work/short.err"
short=$?
"$py" -m tools.benchmark_gate --results-dir "$work/empty" --baseline "$work/baseline.json" 2> "$work/empty.err"
empty=$?
"$py" -m tools.benchmark_gate --results-dir "$work/absent" --baseline "$work/baseline.json" 2> "$work/absent.err"
absent=$?
echo "short lane exit $short, empty file exit $empty, absent binding exit $absent"
[ "$short" -eq 1 ] && [ "$empty" -eq 1 ] && [ "$absent" -eq 0 ] \
  && grep -q "cpp / $other" "$work/short.err" \
  && ! grep -q "cpp / $lane" "$work/short.err" \
  && grep -q "cpp / $lane" "$work/empty.err" \
  && grep -q "cpp / $other" "$work/empty.err"
