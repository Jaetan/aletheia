#!/usr/bin/env bash
# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
#
# Probes docs/MUTATION_BENCH.yaml.
# Claim: the C++ baseline records a run, not a target. The recorded survivor
# count and mutant total are what sweeps of the two configured trees produce,
# merged the way the lane merges them,
# and the sweep's timeouts are within four of the recorded count: a timeout
# is a kill by another route, and its count is not stable for a mutant whose
# behaviour is undefined (a signal count replaced by a constant reads past
# the arrays, crashing on one run and hanging on the next; five sweeps of one
# binary gave 5, 6, 7, 6 and 5), so only a count past that margin is the
# finding, a hang the suite did not have. Non-zero exit: the record and the sweep
# disagree. Exits 0 with a note when Mull or either mutation tree is not
# available, since the claim is untestable then.
set -u
cd "$(dirname "$0")/.." || exit 2
command -v mull-runner-23 > /dev/null || { echo "Mull not installed, claim untestable"; exit 0; }
[ -x cpp/build-mutation/unit_tests ] && [ -x cpp/build-mutation-plain/unit_tests ] ||
    { echo "the mutation trees are not both built, claim untestable"; exit 0; }
py=python/.venv/bin/python
[ -x "$py" ] || exit 2
# ALETHEIA_LIB is unset for the sweep, not merely left alone: with it set the
# integration suite's library lookup returns before it reads the repository
# root, and the two mutants of that read go uncovered, so the same tree scores
# differently for a developer who has sourced the environment script.
# The runner's exit code is not the signal: it exits non-zero when any mutant
# survives, which a baseline above zero guarantees. A sweep that could not run
# leaves no report, and that is what is checked.
# Both trees are swept, because a mutant survives the lane only where every
# lane let it survive: the leak tree reports a destructor removal that leaks,
# the plain tree carries the allocation-fault sweeps, and the two cannot be
# one binary because a sanitizer defines the allocation functions those sweeps
# replace.
for tree in build-mutation build-mutation-plain; do
    rm -f "cpp/$tree/probe-baseline.json"
    (cd "cpp/$tree" &&
        env -u ALETHEIA_LIB ALETHEIA_REPO_ROOT="$OLDPWD" mull-runner-23 ./unit_tests \
            --report-name=probe-baseline --reporters=Elements > /dev/null 2>&1) || true
    [ -s "cpp/$tree/probe-baseline.json" ] || {
        echo "the sweep of $tree produced no report"
        exit 1
    }
done
"$py" - cpp/build-mutation/probe-baseline.json cpp/build-mutation-plain/probe-baseline.json <<'PY'
import collections
import json
import sys

import yaml

sys.path.insert(0, ".")
from tools.mutation_run import merge_elements

TIMEOUT_MARGIN = 4
report = merge_elements(
    [json.load(open(path, encoding="utf-8")) for path in sys.argv[1:]]
)
counts = collections.Counter(
    m["status"] for f in report["files"].values() for m in f.get("mutants", [])
)
observed = {
    "survivors": counts.get("Survived", 0),
    "total_mutants": sum(counts.values()),
    "timeouts": counts.get("Timeout", 0),
}
recorded = yaml.safe_load(open("docs/MUTATION_BENCH.yaml", encoding="utf-8"))
baseline = recorded["bindings"]["cpp"]["baseline"]
bad = {
    k: (baseline.get(k), v)
    for k, v in observed.items()
    if (v > baseline.get(k, 0) + TIMEOUT_MARGIN if k == "timeouts" else baseline.get(k) != v)
}
for key, (was, now) in bad.items():
    print(f"{key}: recorded {was}, a sweep gives {now}")
sys.exit(1 if bad else 0)
PY
