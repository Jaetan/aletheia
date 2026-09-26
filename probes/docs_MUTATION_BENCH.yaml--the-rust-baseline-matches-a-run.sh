#!/usr/bin/env bash
# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
#
# Probes docs/MUTATION_BENCH.yaml.
# Claim: the Rust baseline records a run, not a target.  A sweep of the crate
# under the lane's own command generates the recorded number of mutants, finds
# the recorded number unviable, times out on none, and leaves alive exactly the
# survivors the ledger names, each at its recorded count.
# The generated total and the unviable count are properties of the source and
# of the pinned cargo-mutants; the survivors are properties of the source and
# its tests.  A timed-out mutant is neither killed nor alive, so a run with any
# is a loaded machine's and is refused rather than compared.
# Non-zero exit: the record and a sweep disagree.  Exits 0 with a note when
# cargo-mutants is not installed or the kernel is not built, the claim being
# untestable then.
set -u
cd "$(dirname "$0")/.." || exit 2
py=python/.venv/bin/python
[ -x "$py" ] || exit 2
command -v cargo > /dev/null || { echo "cargo not installed, claim untestable"; exit 0; }
cargo mutants --version > /dev/null 2>&1 || { echo "cargo-mutants not installed, claim untestable"; exit 0; }
[ -f build/libaletheia-ffi.so ] || { echo "no kernel built, claim untestable"; exit 0; }

work=$(mktemp -d) || exit 2
trap 'rm -rf "$work"' EXIT
(cd rust && ALETHEIA_LIB="$OLDPWD/build/libaletheia-ffi.so" \
	cargo mutants --in-place --colors never --output "$work") > "$work/sweep.txt" 2>&1
[ -f "$work/mutants.out/outcomes.json" ] || {
	echo "the sweep wrote no outcomes:"
	tail -3 "$work/sweep.txt" | sed 's/^/  /'
	exit 1
}

"$py" - "$work/mutants.out/outcomes.json" <<'PY'
import json
import sys

sys.path.insert(0, ".")
import yaml

from tools.mutation_run import ledger_to_rows
from tools.mutation_rust import outcomes_survivor_rows, repo_line

outcomes = json.load(open(sys.argv[1], encoding="utf-8"))
record = yaml.safe_load(open("docs/MUTATION_BENCH.yaml", encoding="utf-8"))
baseline = record["bindings"]["rust"]["baseline"]
if outcomes["timeout"]:
    print(f"the sweep timed out on {outcomes['timeout']} mutants: a loaded machine's run, not compared")
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
