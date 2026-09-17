#!/usr/bin/env bash
# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
#
# Probes docs/guides/TUTORIAL.md.
# Claim: the demo run the tutorial prints reports the number of violations the
# tutorial says it does, and exits with the code the tutorial gives for a run
# that found some. Both numbers are in prose, twice each, and nothing ran the
# demo to check them: the count is read out of the guide rather than written
# here, so a guide that says a different number fails.
# Non-zero exit: the run reports something else. Exits 2 without the virtual
# environment, the kernel or the demo files.
set -u
cd "$(dirname "$0")/.." || exit 2
py=python/.venv/bin/python
[ -x "$py" ] || exit 2
[ -f build/libaletheia-ffi.so ] || exit 2
for f in examples/demo/vehicle.dbc examples/demo/vehicle_checks.yaml examples/demo/drive.log; do
	[ -f "$f" ] || exit 2
done
guide=docs/guides/TUTORIAL.md

said=$(grep -oE "reports [0-9]+ timestamped violations" "$guide" | grep -oE "[0-9]+" | head -1)
[ -n "$said" ] || { echo "the guide no longer says how many violations the demo reports"; exit 1; }

work=$(mktemp -d) || exit 2
trap 'rm -rf "$work"' EXIT
ALETHEIA_LIB=$PWD/build/libaletheia-ffi.so "$py" -m aletheia check \
	--dbc examples/demo/vehicle.dbc --checks examples/demo/vehicle_checks.yaml \
	examples/demo/drive.log --json > "$work/out.json" 2> "$work/err.txt"
code=$?

"$py" - "$work/out.json" "$said" "$code" <<'PY'
import json
import sys

report = json.load(open(sys.argv[1], encoding="utf-8"))
said, code = int(sys.argv[2]), int(sys.argv[3])
found = len(report.get("violations", []))
bad = []
if found != said:
    bad.append(f"the run reports {found} violations, the guide says {said}")
if code != 1:
    bad.append(f"the run exits {code}, the guide gives 1 for a run with violations")
if report.get("status") == "pass":
    bad.append("the run passed, so the guide's violating demo no longer violates")
for line in bad:
    print(line)
if bad:
    raise SystemExit(1)
print(f"PASS: the demo reports {found} violations and exits {code}, as the guide says")
PY
