#!/usr/bin/env bash
# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
#
# Probes docs/MUTATION_BENCH.yaml.
# Claim: the C++ baseline's survivors_ledger is exactly what a sweep of the
# configured tree leaves surviving: every survivor is a ledger row, by
# mutator, repository-relative file and source-line text, up to the count
# the row records, and every row still survives. The lane refuses a survivor
# the ledger does not name; this probe also refuses a row that no longer
# survives, which the lane reports as stale and lets pass, so the record is
# lowered by the change that made it stale. Non-zero exit: the ledger and the
# sweep disagree; the diff names each row. Exits 0 with a note when Mull or
# the mutation tree is not available, since the claim is untestable then.
set -u
cd "$(dirname "$0")/.." || exit 2
command -v mull-runner-23 > /dev/null || { echo "Mull not installed, claim untestable"; exit 0; }
[ -x cpp/build-mutation/unit_tests ] || { echo "no mutation tree built, claim untestable"; exit 0; }
py=python/.venv/bin/python
[ -x "$py" ] || exit 2
report=cpp/build-mutation/probe-ledger.json
rm -f "$report"
(cd cpp/build-mutation &&
    env -u ALETHEIA_LIB ALETHEIA_REPO_ROOT="$OLDPWD" mull-runner-23 ./unit_tests \
        --report-name=probe-ledger --reporters=Elements > /dev/null 2>&1) || true
[ -s "$report" ] || {
    echo "the sweep produced no report"
    exit 1
}
"$py" - "$report" <<'PY'
import collections
import json
import sys

import yaml

sys.path.insert(0, ".")
from tools.mutation_run import elements_survivor_rows, ledger_to_rows, rows_to_ledger


def read_line(file, line):
    with open(file, encoding="utf-8") as src:
        return src.read().split("\n")[line - 1]


spec = yaml.safe_load(open("docs/MUTATION_BENCH.yaml", encoding="utf-8"))
ledger = spec["bindings"]["cpp"]["baseline"].get("survivors_ledger")
if ledger is None:
    print("docs/MUTATION_BENCH.yaml records no survivors_ledger for the C++ lane")
    sys.exit(1)
recorded = collections.Counter(ledger_to_rows(ledger))
observed = collections.Counter(
    elements_survivor_rows(json.load(open(sys.argv[1], encoding="utf-8")), read_line)
)
bad = False
for row in rows_to_ledger(dict(observed - recorded)):
    print("survives past the ledger:", row)
    bad = True
for row in rows_to_ledger(dict(recorded - observed)):
    print("in the ledger, no longer survives:", row)
    bad = True
sys.exit(1 if bad else 0)
PY
