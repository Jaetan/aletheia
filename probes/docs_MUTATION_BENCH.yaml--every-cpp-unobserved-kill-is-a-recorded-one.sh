#!/usr/bin/env bash
# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
#
# Probes docs/MUTATION_BENCH.yaml.
# Claim: the C++ baseline's unobserved_ledger is exactly the set of kills the
# two configured trees leave to the standard library's own check or to a bare
# signal, by mutator, repository-relative file, source-line text, route and
# the invariant refused, up to the count each row records. Both directions
# are refused here: the lane refuses a kill the ledger does not name and only
# reports a row the sweep no longer produces, so that a test which learned to
# observe one does not fail the change that wrote it; this refuses the stale
# row too, so the record is lowered rather than carried.
# The static gate (tools/check_mutation_setup.py) holds each row to a line the
# tree still has and needs no sweep; this holds the rows to what a sweep
# actually reads, which is the half no file comparison can answer.
# The runner's argv is the lane's own, so the cap per mutant and the pinned
# order have one owner: an unpinned order moves which test reports before a
# dying process stops, and a mutant the runner ends at its cap is neither
# killed nor surviving and would leave the ledger's candidates unread.
# Non-zero exit: the ledger and the sweep disagree; the diff names each row.
# Exits 0 with a note when Mull or either mutation tree is not available,
# since the claim is untestable then.
set -u
cd "$(dirname "$0")/.." || exit 2
command -v mull-runner-23 > /dev/null || { echo "Mull not installed, claim untestable"; exit 0; }
py=python/.venv/bin/python
[ -x "$py" ] || exit 2
# The trees are the ones the lane sweeps, read from the lane rather than named
# here, so a tree the lane gains is a tree this probe reads.
trees=$("$py" -c 'from tools.mutation_cpp import CppTree
print(" ".join(tree.value for tree in CppTree))') || exit 2
for lane in $trees; do
    built=$("$py" -c 'import sys
from tools.mutation_cpp import CppTree
print(CppTree(sys.argv[1]).directory)' "$lane") || exit 2
    [ -x "cpp/$built/unit_tests" ] ||
        { echo "the $lane mutation tree is not built, claim untestable"; exit 0; }
done
# One sweep serves every probe that reads one: tools/mutation_sweep_cache.py
# runs it once, keyed on each tree's test binary and the lane's own argv, so a
# second reader pays nothing and a rebuilt tree is swept again. The lane's
# environment and the runner's arguments are the lane's own, built by
# tools/mutation_cpp.py, so the cap per mutant and the pinned order have one
# owner.
dir=$("$py" -m tools.mutation_sweep_cache) || {
    echo "no sweep of the mutation trees could be had"
    exit 2
}
"$py" - "$dir" <<'PY'
import collections
import sys
from pathlib import Path

import yaml

sys.path.insert(0, ".")
from tools.mutation_cpp import CppTree, _repo_line, unobserved_kill_rows
from tools.mutation_report import unobserved_ledger_to_rows, unobserved_rows_to_ledger
from tools.mutation_routes import lane_endings

spec = yaml.safe_load(open("docs/MUTATION_BENCH.yaml", encoding="utf-8"))
ledger = spec["bindings"]["cpp"]["baseline"].get("unobserved_ledger")
if ledger is None:
    print("docs/MUTATION_BENCH.yaml records no unobserved_ledger for the C++ lane")
    sys.exit(1)
reports = [Path(sys.argv[1]) / f"cpp-mull-{tree.value}.sqlite" for tree in CppTree]
observed = collections.Counter(
    unobserved_kill_rows([lane_endings(path) for path in reports], _repo_line)
)
recorded = collections.Counter(unobserved_ledger_to_rows(ledger))
bad = False
for row in unobserved_rows_to_ledger(dict(observed - recorded)):
    print("no test observes it and the ledger does not name it:", row)
    bad = True
for row in unobserved_rows_to_ledger(dict(recorded - observed)):
    print("in the ledger, no longer an unobserved kill:", row)
    bad = True
if not bad:
    print(
        f"PASS: {len(ledger)} rows, "
        + f"{sum(row['count'] for row in ledger)} mutants, the sweep reads the same"
    )
sys.exit(1 if bad else 0)
PY
