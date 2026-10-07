#!/usr/bin/env bash
# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
#
# Probes docs/MUTATION_BENCH.yaml.
# Claim: the Go baseline records a run, not a target. A sweep of the package
# by the lane's own runner generates the recorded number of mutants, finds the
# recorded number on lines no test reaches, and leaves alive exactly the
# survivors the ledger names, each at its recorded count.
# The generated total and the not-covered count are properties of the source
# and its tests, the survivors of the source and its tests. A timed-out mutant
# is neither killed nor alive, and none can hang a run by construction, so a
# run in which gremlins' cap fired more often than the record's ceiling allows
# is a disturbed run and is refused rather than compared.
# The sweep is tools/mutation_run.py's, which tests each mutant against a
# scratch copy of the tree, so no tracked file moves while it runs, and it is
# kept (tools/mutation_sweep_cache.py), so it runs only where no sweep of the
# tree as it stands, with the library and the toolchain, is kept.
# Non-zero exit: the record and a sweep disagree, or the sweep did not run.
# Exits 0 with a note when gremlins is not installed or the kernel is not
# built, the claim being untestable then.
set -u
cd "$(dirname "$0")/.." || exit 2
export PATH="$PATH:$HOME/go/bin"
command -v gremlins > /dev/null || { echo "gremlins not installed, claim untestable"; exit 0; }
py=python/.venv/bin/python
[ -x "$py" ] || exit 2
[ -f build/libaletheia-ffi.so ] || { echo "no kernel built, claim untestable"; exit 0; }

"$py" - <<'PY'
import re
import sys
from pathlib import Path

sys.path.insert(0, ".")
import yaml

from tools.mutation_run import go_mutant_rows, ledger_to_rows
from tools.mutation_sweep_cache import LANE_REPORT, lane_sweep_directory

kept = lane_sweep_directory("go")
if not isinstance(kept, Path):
    print(f"the sweep did not run: {kept}")
    raise SystemExit(1)
raw = (kept / LANE_REPORT["go"]).read_text(encoding="utf-8")
counts = {}
for name, key in (("Killed", "killed"), ("Lived", "survivors"), ("Not covered", "not_covered"),
                  ("Timed out", "timeouts"), ("Not viable", "not_viable"), ("Skipped", "skipped")):
    match = re.search(rf"{name}:\s*(\d+)", raw)
    if match is None:
        print(f"the sweep's summary carries no {name} count")
        raise SystemExit(1)
    counts[key] = int(match.group(1))
record = yaml.safe_load(open("docs/MUTATION_BENCH.yaml", encoding="utf-8"))
baseline = record["bindings"]["go"]["baseline"]
if counts["timeouts"] > baseline["timeout_ceiling"]:
    print(f"the sweep timed out on {counts['timeouts']} mutants: a disturbed run, not compared")
    raise SystemExit(1)
observed = {"survivors": counts["survivors"], "generated": sum(counts.values()),
            "not_covered": counts["not_covered"]}
bad = {k: (baseline.get(k), v) for k, v in observed.items() if baseline.get(k) != v}
for key, (was, now) in bad.items():
    print(f"{key}: recorded {was}, a sweep gives {now}")
for ledger, verdict in (("survivors_ledger", "LIVED"), ("not_covered_ledger", "NOT COVERED")):
    rows = go_mutant_rows(raw, verdict)
    recorded = ledger_to_rows(baseline.get(ledger, []))
    for key in sorted(set(rows) | set(recorded)):
        if rows.get(key, 0) != recorded.get(key, 0):
            print(f"{ledger} {key}: recorded {recorded.get(key, 0)}, a sweep gives {rows.get(key, 0)}")
            bad[key] = True
if bad:
    raise SystemExit(1)
print(f"PASS: the Go baseline records a run ({observed['generated']} generated, "
      f"{observed['survivors']} alive, {observed['not_covered']} not covered, every row a recorded one)")
PY
