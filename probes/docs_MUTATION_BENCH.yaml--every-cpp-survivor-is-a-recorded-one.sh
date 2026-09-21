#!/usr/bin/env bash
# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
#
# Probes docs/MUTATION_BENCH.yaml.
# Claim: the C++ baseline's survivors_ledger is exactly what the two
# configured trees leave surviving between them: every survivor is a ledger row, by
# mutator, repository-relative file and source-line text, up to the count
# the row records, and every row still survives. The lane refuses a survivor
# the ledger does not name; this probe also refuses a row that no longer
# survives, which the lane reports as stale and lets pass, so the record is
# lowered by the change that made it stale. Non-zero exit: the ledger and the
# sweep disagree; the diff names each row. Exits 0 with a note when Mull or
# either mutation tree is not available, since the claim is untestable then.
set -u
cd "$(dirname "$0")/.." || exit 2
command -v mull-runner-23 > /dev/null || { echo "Mull not installed, claim untestable"; exit 0; }
[ -x cpp/build-mutation/unit_tests ] && [ -x cpp/build-mutation-plain/unit_tests ] ||
    { echo "the mutation trees are not both built, claim untestable"; exit 0; }
py=python/.venv/bin/python
[ -x "$py" ] || exit 2
# Both trees are swept, because a mutant survives the lane only where every
# lane let it survive: the leak tree reports a destructor removal that leaks,
# the plain tree carries the allocation-fault sweeps, and the two cannot be
# one binary because a sanitizer defines the allocation functions those sweeps
# replace.
# The runner's argv is the lane's own, built by tools/mutation_cpp.py, so the
# cap per mutant and the pinned order have one owner; only where the reports
# land is this probe's. Both matter to this claim: a mutant the runner ends at
# its cap is neither killed nor surviving, so it would leave the ledger's
# candidates without being read, and an unpinned order decides which test
# reports before a dying process stops.
dir=$(mktemp -d) || exit 2
trap 'rm -rf "$dir"' EXIT
for lane in leak plain; do
    argv=$("$py" -c 'import shlex, sys
from pathlib import Path
from tools.mutation_cpp import CppLeg, CppTree, cpp_lane_command
leg = CppLeg(CppTree(sys.argv[2]))
print(shlex.join(cpp_lane_command("mull-runner-23", Path("cpp", leg.directory).resolve(), Path(sys.argv[1]), leg)))' "$dir" "$lane") || exit 2
    (cd cpp && unset ALETHEIA_LIB && ALETHEIA_REPO_ROOT="$OLDPWD" eval "$argv" > /dev/null 2>&1) || true
    [ -s "$dir/cpp-mull-$lane.json" ] || {
        echo "the sweep of the $lane tree produced no report"
        exit 1
    }
done
"$py" - "$dir/cpp-mull-leak.json" "$dir/cpp-mull-plain.json" <<'PY'
import collections
import json
import sys

import yaml

sys.path.insert(0, ".")
from tools.mutation_cpp import elements_survivor_rows, merge_elements
from tools.mutation_run import ledger_to_rows, rows_to_ledger


def read_line(file, line):
    with open(file, encoding="utf-8") as src:
        return src.read().split("\n")[line - 1]


spec = yaml.safe_load(open("docs/MUTATION_BENCH.yaml", encoding="utf-8"))
ledger = spec["bindings"]["cpp"]["baseline"].get("survivors_ledger")
if ledger is None:
    print("docs/MUTATION_BENCH.yaml records no survivors_ledger for the C++ lane")
    sys.exit(1)
recorded = collections.Counter(ledger_to_rows(ledger))
merged = merge_elements([json.load(open(path, encoding="utf-8")) for path in sys.argv[1:]])
observed = collections.Counter(elements_survivor_rows(merged, read_line))
bad = False
for row in rows_to_ledger(dict(observed - recorded)):
    print("survives past the ledger:", row)
    bad = True
for row in rows_to_ledger(dict(recorded - observed)):
    print("in the ledger, no longer survives:", row)
    bad = True
sys.exit(1 if bad else 0)
PY
