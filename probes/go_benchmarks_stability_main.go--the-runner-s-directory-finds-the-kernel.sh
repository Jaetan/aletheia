#!/usr/bin/env bash
# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
#
# Probes go/benchmarks/stability/main.go.
# Claim: with nothing in the environment the harness finds the built kernel from
# the repo root, from go/ where tools/stability_run.py runs it, and from its own
# directory. The runner sets the path itself, so the search answers only to
# someone running the harness by hand, which is when a candidate resolving from
# none of these directories goes unnoticed.
# The binary is built into a temporary directory so the candidate taken from the
# executable's own location cannot resolve, leaving the working directory to
# answer.
# Non-zero exit: a directory the harness is run from cannot find the kernel.
# Exits 2 without Go or without a built kernel.
set -u
cd "$(dirname "$0")/.." || exit 2
root=$PWD
command -v go > /dev/null || exit 2
[ -f "$root/build/libaletheia-ffi.so" ] || exit 2

work=$(mktemp -d) || exit 2
trap 'rm -rf "$work"' EXIT
(cd go && go build -o "$work/stability" ./benchmarks/stability/) || exit 2

unset ALETHEIA_LIB
export ALETHEIA_STABILITY_CYCLES=1 ALETHEIA_STABILITY_FRAMES=10
failed=0
for from in "$root" "$root/go" "$root/go/benchmarks/stability"; do
	if ! (cd "$from" && "$work/stability") > "$work/out.json" 2> "$work/err.txt"; then
		echo "from ${from#"$root"}/: $(grep -m1 . "$work/err.txt")"
		failed=1
	fi
done

[ "$failed" -eq 0 ] || exit 1
echo "PASS: the kernel is found from the repo root, from go/ and from the harness's own directory"
