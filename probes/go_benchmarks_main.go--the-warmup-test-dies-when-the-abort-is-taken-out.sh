#!/usr/bin/env bash
# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
#
# Probes go/benchmarks/main.go and go/benchmarks/main_test.go.
# Claim: the test that holds the throughput lane to aborting on a failed
# warmup is not vacuous. The warmup's error arm is replaced by a report that
# continues, in a copy of the source the test build reads through an overlay,
# and the lane tests must fail against it and pass against the tracked
# source; the tracked file is not written.
# Non-zero exit: the tests pass with the abort taken out, or fail with it in
# place. Exits 2 without Go.
set -u
cd "$(dirname "$0")/.." || exit 2
command -v go > /dev/null || exit 2

work=$(mktemp -d) || exit 2
trap 'rm -rf "$work"' EXIT
src=$PWD/go/benchmarks/main.go
arm='return throughputResult{}, fmt.Errorf("lane %q warmup %d/%d failed: %w", name, w+1, warmupRuns, err)'
grep -qF "$arm" "$src" || { echo "the warmup abort is not written where this probe mutates it"; exit 1; }
sed "s#$arm#fmt.Fprintf(out, \"  Warmup error: %v\\\\n\", err)#" "$src" > "$work/main.go"
grep -q 'Warmup error' "$work/main.go" || { echo "the mutation did not land"; exit 2; }
printf '{"Replace": {"%s": "%s"}}\n' "$src" "$work/main.go" > "$work/overlay.json"

cpus="0-$(($(nproc) - 2))"
cd go || exit 2
if ! taskset -c "$cpus" go test ./benchmarks -run TestThroughputLane -count=1 > "$work/intact.txt" 2>&1; then
	echo "the lane tests fail against the tracked source:"
	tail -5 "$work/intact.txt" | sed 's/^/  /'
	exit 1
fi
if taskset -c "$cpus" go test -overlay "$work/overlay.json" ./benchmarks -run TestThroughputLane -count=1 > "$work/mutant.txt" 2>&1; then
	echo "the lane tests pass with the warmup abort replaced by a report"
	exit 1
fi
grep -q 'does not name "warmup 1/2"' "$work/mutant.txt" || {
	echo "the tests failed against the mutant for some other reason:"
	tail -5 "$work/mutant.txt" | sed 's/^/  /'
	exit 1
}
echo "PASS: the lane tests die when the warmup abort is taken out"
