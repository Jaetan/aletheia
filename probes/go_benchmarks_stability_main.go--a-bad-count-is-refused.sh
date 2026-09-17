#!/usr/bin/env bash
# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
#
# Probes go/benchmarks/stability/main.go.
# Claim: ALETHEIA_STABILITY_CYCLES and ALETHEIA_STABILITY_FRAMES accept only a
# positive whole number, and anything else is refused by name with the exit code
# tools/stability_run.py reads as an environment failure. A value silently
# replaced by the default runs a measurement nobody asked for and reports it as
# the answer, and the C++ harness refuses the same values the same way.
# Non-zero exit: a bad value was accepted, or refused without saying so. Exits 2
# without Go or without a built kernel.
set -u
cd "$(dirname "$0")/.." || exit 2
command -v go > /dev/null || exit 2
lib=$PWD/build/libaletheia-ffi.so
[ -f "$lib" ] || exit 2

work=$(mktemp -d) || exit 2
trap 'rm -rf "$work"' EXIT
(cd go && go build -o "$work/stability" ./benchmarks/stability/) || exit 2

export ALETHEIA_LIB=$lib LD_LIBRARY_PATH=$PWD/build
failed=0
refuses() {
	env "$1=$2" "$3=1" "$work/stability" > "$work/out.json" 2> "$work/stderr.txt"
	status=$?
	if [ "$status" -eq 0 ]; then
		echo "accepted $1='$2'"
		failed=1
	elif [ "$status" -eq 1 ]; then
		echo "$1='$2' was reported as drift, not as a bad value"
		failed=1
	elif ! grep -q "$1 must be a positive whole number" "$work/stderr.txt"; then
		echo "$1='$2' failed without naming the variable:"
		tail -2 "$work/stderr.txt" | sed 's/^/    /'
		failed=1
	fi
}
for bad in abc 0 -3 5x ""; do
	refuses ALETHEIA_STABILITY_CYCLES "$bad" ALETHEIA_STABILITY_FRAMES
	refuses ALETHEIA_STABILITY_FRAMES "$bad" ALETHEIA_STABILITY_CYCLES
done

[ "$failed" -eq 0 ] || exit 1
echo "PASS: every value that is not a positive whole number is refused by name"
