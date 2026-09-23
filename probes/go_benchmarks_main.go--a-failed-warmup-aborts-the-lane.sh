#!/usr/bin/env bash
# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
#
# Probes go/benchmarks/main.go.
# Claim: a throughput lane whose warmup operation fails aborts the benchmark
# with the lane, the pass and the error named, before any measured run. A
# harness that continued past a failed warmup measured a client it could not
# drive, and either published a number for it or died later on the measured
# run with the warmup's message gone. No real kernel fails a warmup from
# outside, so the lane's operation is replaced by one that fails on every
# call, in a copy of the source the build reads through an overlay; the
# tracked file is not written. The copy also imports errors, so the build
# exits 2 rather than 1 should the harness come to import it itself.
# Non-zero exit: the benchmark exited zero, died without naming the warmup
# pass, or reached a measured run. Exits 2 without Go or a built kernel.
set -u
cd "$(dirname "$0")/.." || exit 2
command -v go > /dev/null || exit 2
lib=$PWD/build/libaletheia-ffi.so
[ -f "$lib" ] || exit 2

work=$(mktemp -d) || exit 2
trap 'rm -rf "$work"' EXIT
src=$PWD/go/benchmarks/main.go
grep -q '^func throughputLane(' "$src" || { echo "the lane function is not where this probe injects"; exit 1; }
sed -e '/^func throughputLane(/a\
	run = func(int) (float64, error) { return 0, errors.New("injected warmup failure") }' \
	-e 's#^\t"encoding/json"$#\t"encoding/json"\n\t"errors"#' "$src" > "$work/main.go"
printf '{"Replace": {"%s": "%s"}}\n' "$src" "$work/main.go" > "$work/overlay.json"
cpus="0-$(($(nproc) - 2))"
(cd go && taskset -c "$cpus" go build -overlay "$work/overlay.json" -o "$work/benchmark" ./benchmarks) || exit 2

export ALETHEIA_LIB=$lib LD_LIBRARY_PATH=$PWD/build
if "$work/benchmark" throughput --frames 100 --runs 1 --warmup 2 --json > "$work/out.txt" 2> "$work/err.txt"; then
	echo "the benchmark exited 0 with every warmup failing"
	exit 1
fi
failed=0
if ! grep -q 'warmup 1/2 failed: injected warmup failure' "$work/err.txt"; then
	echo "the benchmark died without naming the failed warmup pass:"
	tail -3 "$work/err.txt" | sed 's/^/  /'
	failed=1
fi
if grep -qi 'run 1/' "$work/err.txt" "$work/out.txt"; then
	echo "a measured run followed the failed warmup"
	failed=1
fi
[ "$failed" -eq 0 ] || exit 1
echo "PASS: a failed warmup aborts the lane before any measured run, naming the pass"
