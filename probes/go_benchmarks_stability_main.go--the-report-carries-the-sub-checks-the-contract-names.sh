#!/usr/bin/env bash
# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
#
# Probes go/benchmarks/stability/main.go.
# Claim: the report the harness writes carries exactly the sub-checks
# docs/STABILITY_BENCH.yaml declares for this binding, each under the gate word
# the contract gives it, and every exact gate reports a threshold of zero.
# tools/check_stability_bench.py holds the same contract by grepping the source
# for a marker, which a harness can carry while reporting something else; this
# runs the harness and reads what it reported.
# The binary is built, never found: one left over from before a change reports a
# shape that is void rather than stale.
# Non-zero exit: the report has left the contract. Exits 2 without Go or without
# a built kernel.
set -u
cd "$(dirname "$0")/.." || exit 2
command -v go > /dev/null || exit 2
lib=$PWD/build/libaletheia-ffi.so
[ -f "$lib" ] || exit 2
py=python/.venv/bin/python
[ -x "$py" ] || exit 2

work=$(mktemp -d) || exit 2
trap 'rm -rf "$work"' EXIT
(cd go && go build -o "$work/stability" ./benchmarks/stability/) || exit 2

export ALETHEIA_LIB=$lib LD_LIBRARY_PATH=$PWD/build
ALETHEIA_STABILITY_CYCLES=2 ALETHEIA_STABILITY_FRAMES=200 \
	"$work/stability" > "$work/report.json" 2> "$work/stderr.txt"
status=$?
if [ "$status" -ne 0 ]; then
	echo "the harness exited $status on a short run:"
	tail -3 "$work/stderr.txt" | sed 's/^/  /'
	exit 1
fi

"$py" - "$work" <<'PY'
import json
import sys

import yaml

report = json.load(open(f"{sys.argv[1]}/report.json", encoding="utf-8"))
contract = yaml.safe_load(open("docs/STABILITY_BENCH.yaml", encoding="utf-8"))["bindings"]["go"]["sub_checks"]
bad = []

want = [(c["name"], c["gate"]) for c in contract]
got = [(c["name"], c["gate"]) for c in report["sub_checks"]]
if sorted(got) != sorted(want):
    bad.append(f"sub-checks {sorted(got)} != {sorted(want)}")

for check in report["sub_checks"]:
    if check["gate"] == "hard_zero":
        if check["threshold"] != 0:
            bad.append(f"{check['name']}: an exact gate carries a threshold of {check['threshold']}")
        if check["passed"] != (check["delta"] == 0):
            bad.append(f"{check['name']}: delta {check['delta']} with passed {check['passed']}")
    if check["end"] - check["start"] != check["delta"]:
        bad.append(f"{check['name']}: {check['end']} minus {check['start']} is not {check['delta']}")

if report["total_frames"] != report["cycles"] * report["frames_per_cycle"]:
    bad.append("the total does not multiply out")
if report["passed"] != all(c["passed"] for c in report["sub_checks"]):
    bad.append("the verdict does not follow from the sub-checks")
if report["binding"] != "go":
    bad.append(f"the report names the binding {report['binding']!r}")

if bad:
    print("the Go stability report has left docs/STABILITY_BENCH.yaml:")
    for line in bad:
        print(f"  {line}")
    raise SystemExit(1)
print("PASS: the report carries the sub-checks the contract names")
PY
