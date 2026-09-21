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
[ -x cpp/build-mutation/unit_tests ] && [ -x cpp/build-mutation-plain/unit_tests ] ||
    { echo "the mutation trees are not both built, claim untestable"; exit 0; }
py=python/.venv/bin/python
[ -x "$py" ] || exit 2
dir=$(mktemp -d) || exit 2
trap 'rm -rf "$dir"' EXIT
# Both trees, because a kill is attributed across them: a mutant a test
# observes in either is not an unobserved kill, whatever the other read.
for lane in leak plain; do
    argv=$("$py" -c 'import shlex, sys
from pathlib import Path
from tools.mutation_cpp import CppLeg, CppTree, cpp_lane_command
leg = CppLeg(CppTree(sys.argv[2]))
print(shlex.join(cpp_lane_command("mull-runner-23", Path("cpp", leg.directory).resolve(), Path(sys.argv[1]), leg)))' "$dir" "$lane") || exit 2
    (cd cpp && unset ALETHEIA_LIB && ALETHEIA_REPO_ROOT="$OLDPWD" eval "$argv" > /dev/null 2>&1) || true
    [ -f "$dir/cpp-mull-$lane.sqlite" ] || {
        echo "the sweep of the $lane tree wrote no SQLite report"
        exit 1
    }
done
"$py" - "$dir" <<'PY'
import collections
import sys
from pathlib import Path

import yaml

sys.path.insert(0, ".")
from tools.mutation_cpp import _repo_line, unobserved_kill_rows
from tools.mutation_report import unobserved_ledger_to_rows, unobserved_rows_to_ledger
from tools.mutation_routes import lane_endings

spec = yaml.safe_load(open("docs/MUTATION_BENCH.yaml", encoding="utf-8"))
ledger = spec["bindings"]["cpp"]["baseline"].get("unobserved_ledger")
if ledger is None:
    print("docs/MUTATION_BENCH.yaml records no unobserved_ledger for the C++ lane")
    sys.exit(1)
reports = [Path(sys.argv[1]) / f"cpp-mull-{lane}.sqlite" for lane in ("leak", "plain")]
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
