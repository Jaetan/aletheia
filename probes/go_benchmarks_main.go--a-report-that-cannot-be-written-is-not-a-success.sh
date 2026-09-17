#!/usr/bin/env bash
# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
#
# Probes go/benchmarks/main.go.
# Claim: when the JSON report cannot be written the benchmark exits non-zero.
# benchmarks/run_all.sh redirects this stream into a results file, so an exit of
# zero over a truncated or empty one is read as a healthy run and lands in the
# comparison as a binding that measured nothing.
# The write is made to fail by sending it to /dev/full, which accepts an open
# and refuses every write with ENOSPC.
# Non-zero exit: the benchmark reported success without writing its report.
# Exits 2 without Go, without a built kernel, or without /dev/full.
set -u
cd "$(dirname "$0")/.." || exit 2
command -v go > /dev/null || exit 2
lib=$PWD/build/libaletheia-ffi.so
[ -f "$lib" ] || exit 2
[ -c /dev/full ] || exit 2

work=$(mktemp -d) || exit 2
trap 'rm -rf "$work"' EXIT
(cd go && go build -o "$work/benchmark" ./benchmarks) || exit 2

export ALETHEIA_LIB=$lib LD_LIBRARY_PATH=$PWD/build
"$work/benchmark" throughput --frames 10 --runs 1 --warmup 0 --json \
	> /dev/full 2> "$work/stderr.txt"
status=$?
if [ "$status" -eq 0 ]; then
	echo "the report could not be written and the benchmark exited 0"
	exit 1
fi
if ! grep -q "report failed" "$work/stderr.txt"; then
	echo "the benchmark failed without saying the report could not be written:"
	tail -3 "$work/stderr.txt" | sed 's/^/  /'
	exit 1
fi
echo "PASS: an unwritable report exits $status and says so"
