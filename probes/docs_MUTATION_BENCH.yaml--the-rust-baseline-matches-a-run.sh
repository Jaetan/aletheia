#!/usr/bin/env bash
# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
#
# Probes docs/MUTATION_BENCH.yaml.
# Claim: the Rust baseline records a run, not a target.  A sweep of the crate
# by the lane's own tool generates the recorded number of mutants, finds the
# recorded number unviable, times out on none, and leaves alive exactly the
# survivors the ledger names, each at its recorded count.
# The generated total and the unviable count are properties of the source and
# of the pinned cargo-mutants; the survivors are properties of the source and
# its tests.  A timed-out mutant is neither killed nor alive, so a run with any
# is a disturbed run and is refused rather than compared.
# The sweep is tools/mutation_rust.py's, which mutates scratch copies of the
# tree, so no tracked file moves while it runs, and it is kept
# (tools/mutation_sweep_cache.py), so it runs only where no sweep of the tree
# as it stands, with the library and the toolchain, is kept.
# Non-zero exit: the record and a sweep disagree, or the tool refused to sweep.
# Exits 0 with a note when cargo-mutants is not installed or the kernel is not
# built, the claim being untestable then.
set -u
cd "$(dirname "$0")/.." || exit 2
py=python/.venv/bin/python
[ -x "$py" ] || exit 2
command -v cargo > /dev/null || { echo "cargo not installed, claim untestable"; exit 0; }
cargo mutants --version > /dev/null 2>&1 || { echo "cargo-mutants not installed, claim untestable"; exit 0; }
[ -f build/libaletheia-ffi.so ] || { echo "no kernel built, claim untestable"; exit 0; }

"$py" - <<'PY'
import json
import sys
from pathlib import Path

sys.path.insert(0, ".")
import yaml

from tools.mutation_run import ledger_to_rows
from tools.mutation_rust import outcomes_survivor_rows, repo_line
from tools.mutation_sweep_cache import LANE_REPORT, lane_sweep_directory

kept = lane_sweep_directory("rust")
if not isinstance(kept, Path):
    print(f"the sweep did not run: {kept}")
    raise SystemExit(1)
outcomes = json.load(open(kept / LANE_REPORT["rust"], encoding="utf-8"))
record = yaml.safe_load(open("docs/MUTATION_BENCH.yaml", encoding="utf-8"))
baseline = record["bindings"]["rust"]["baseline"]
if outcomes["timeout"]:
    print(f"the sweep timed out on {outcomes['timeout']} mutants: a disturbed run, not compared")
    raise SystemExit(1)
observed = {
    "generated": outcomes["total_mutants"],
    "unviable": outcomes["unviable"],
    "survivors": outcomes["missed"],
}
bad = {k: (baseline.get(k), v) for k, v in observed.items() if baseline.get(k) != v}
for key, (was, now) in bad.items():
    print(f"{key}: recorded {was}, a sweep gives {now}")
rows = outcomes_survivor_rows(outcomes, repo_line)
recorded = ledger_to_rows(baseline.get("survivors_ledger", []))
for key in sorted(set(rows) | set(recorded)):
    if rows.get(key, 0) != recorded.get(key, 0):
        print(f"survivor {key}: recorded {recorded.get(key, 0)}, a sweep gives {rows.get(key, 0)}")
        bad[key] = True
if bad:
    raise SystemExit(1)
print(f"PASS: the Rust baseline records a run ({observed['generated']} generated, "
      f"{observed['unviable']} unviable, {observed['survivors']} alive, every survivor a recorded row)")
PY
