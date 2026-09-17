#!/usr/bin/env bash
# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
#
# Probes go/benchmarks/stability/main.go.
# Claim: the harness has teeth on its exact handle gate. A variant of the same
# source whose cycle never closes its client fails, with stableptr marked not
# passed and the exit code that carries a verdict, while the tracked source
# passes the same short run. Both are built here from the tracked file, so what
# is measured is the harness as it stands rather than a binary left over from
# an earlier state of it.
# Non-zero exit: the leaking variant passed, or the tracked one failed. Exits 2
# without Go or without a built kernel.
set -u
cd "$(dirname "$0")/.." || exit 2
command -v go > /dev/null || exit 2
lib=$PWD/build/libaletheia-ffi.so
[ -f "$lib" ] || exit 2

work=$(mktemp -d) || exit 2
trap 'rm -rf "$work"' EXIT
src=go/benchmarks/stability/main.go
sed 's|^\tdefer client.Close()$|\t// the close this variant leaves out|' "$src" > "$work/leaky.go"
if ! grep -q "this variant leaves out" "$work/leaky.go"; then
	echo "the close the variant removes is not where the probe looked for it"
	exit 1
fi

(cd go && go build -o "$work/clean" ./benchmarks/stability/) || exit 2
(cd go && go build -o "$work/leaky" "$work/leaky.go") || exit 2

export ALETHEIA_LIB=$lib LD_LIBRARY_PATH=$PWD/build
export ALETHEIA_STABILITY_CYCLES=2 ALETHEIA_STABILITY_FRAMES=200
if ! "$work/clean" > "$work/clean.json" 2> "$work/clean.err"; then
	echo "the tracked harness failed a short run:"
	tail -3 "$work/clean.err" | sed 's/^/  /'
	exit 1
fi
"$work/leaky" > "$work/leaky.json" 2> /dev/null
status=$?
if [ "$status" -eq 0 ]; then
	echo "the variant that never closes its client passed"
	exit 1
fi
if [ "$status" -ne 1 ]; then
	echo "the leaking variant exited $status, which carries no verdict"
	exit 1
fi
python3 - "$work/leaky.json" <<'PY'
import json
import sys

report = json.load(open(sys.argv[1], encoding="utf-8"))
handles = next(c for c in report["sub_checks"] if c["name"] == "stableptr")
if handles["passed"] or handles["delta"] <= 0:
    print(f"the handle gate did not catch it: {handles}")
    raise SystemExit(1)
print(f"PASS: a client left open drifts the handle count by {handles['delta']} and fails the gate")
PY
