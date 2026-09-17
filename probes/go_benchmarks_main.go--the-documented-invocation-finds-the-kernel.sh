#!/usr/bin/env bash
# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
#
# Probes go/benchmarks/main.go.
# Claim: with nothing in the environment, the benchmark finds the built kernel
# from each of the three working directories it is run from: the repo root, go/
# where its own usage line says to run it, and go/benchmarks/. The library
# search is what makes that true, and a candidate that resolves from none of
# them documents an invocation that cannot work.
# The binary is built into a temporary directory so the candidate taken from the
# executable's own location cannot resolve, leaving the working directory to
# answer. The usage line's command is then run as written.
# Non-zero exit: an invocation the file documents cannot load the kernel. Exits
# 2 without Go or without a built kernel.
set -u
cd "$(dirname "$0")/.." || exit 2
root=$PWD
command -v go > /dev/null || exit 2
[ -f "$root/build/libaletheia-ffi.so" ] || exit 2

work=$(mktemp -d) || exit 2
trap 'rm -rf "$work"' EXIT
(cd go && go build -o "$work/benchmark" ./benchmarks) || exit 2

unset ALETHEIA_LIB
failed=0
for from in "$root" "$root/go" "$root/go/benchmarks"; do
	if ! (cd "$from" && "$work/benchmark" throughput --frames 10 --runs 1 --warmup 0) \
		> "$work/out.txt" 2>&1; then
		echo "from ${from#"$root"}/: $(grep -m1 failed "$work/out.txt")"
		failed=1
	fi
done

if ! (cd "$root/go" && go run ./benchmarks throughput --frames 10 --runs 1 --warmup 0) \
	> "$work/run.txt" 2>&1; then
	echo "the usage line's own command fails: $(grep -m1 'failed' "$work/run.txt")"
	failed=1
fi

[ "$failed" -eq 0 ] || exit 1
echo "PASS: the kernel is found from the repo root, from go/ and from go/benchmarks/"
