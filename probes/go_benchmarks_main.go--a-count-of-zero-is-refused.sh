#!/usr/bin/env bash
# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
#
# Probes go/benchmarks/main.go.
# Claim: a run asked for no frames, no runs or no operations is refused before
# anything is measured. A lane measured over nothing publishes a rate of zero
# with every other field filled in, which is conformant with
# benchmarks/SCHEMA.yaml and reads as a slow binding rather than as a failure.
# benchmarks/run_all.sh refuses non-positive counts of its own, and this is the
# same refusal in the binary, which the schema gate and a person at a terminal
# run directly.
# Non-zero exit: a count of zero was accepted. Exits 2 without Go or without a
# built kernel.
set -u
cd "$(dirname "$0")/.." || exit 2
command -v go > /dev/null || exit 2
lib=$PWD/build/libaletheia-ffi.so
[ -f "$lib" ] || exit 2

work=$(mktemp -d) || exit 2
trap 'rm -rf "$work"' EXIT
(cd go && go build -o "$work/benchmark" ./benchmarks) || exit 2

export ALETHEIA_LIB=$lib LD_LIBRARY_PATH=$PWD/build
failed=0
# The refusal is asked for by name, not merely a non-zero exit: with the check
# gone some of these reach the statistics and die on an empty slice, which is a
# crash rather than a refusal and leaves a stack trace where a message belongs.
check() {
	if "$work/benchmark" "$@" --json > "$work/out.json" 2> "$work/stderr.txt"; then
		echo "accepted: $*"
		failed=1
	elif ! grep -qE "must be at least 1|must not be negative" "$work/stderr.txt"; then
		echo "not refused, but failed some other way: $*"
		tail -2 "$work/stderr.txt" | sed 's/^/    /'
		failed=1
	fi
}
check throughput --frames 0 --runs 1 --warmup 0
check throughput --frames 100 --runs 0 --warmup 0
check latency --ops 0 --warmup 0
check scaling --quick --runs 0
check throughput --frames 100 --runs 1 --warmup -1
check throughput --frames -100 --runs 1 --warmup 0

[ "$failed" -eq 0 ] || exit 1
echo "PASS: every non-positive count is refused"
