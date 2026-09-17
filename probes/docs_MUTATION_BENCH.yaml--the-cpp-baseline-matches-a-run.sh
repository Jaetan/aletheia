#!/usr/bin/env bash
# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
#
# Probes docs/MUTATION_BENCH.yaml.
# Claim: the C++ baseline records a run, not a target. The recorded survivor
# count, mutant total and timeout count are what a sweep of the configured
# tree produces. Non-zero exit: the record and the sweep disagree. Exits 0
# with a note when Mull or the mutation tree is not available, since the
# claim is untestable then.
set -u
cd "$(dirname "$0")/.." || exit 2
command -v mull-runner-23 > /dev/null || { echo "Mull not installed, claim untestable"; exit 0; }
[ -x cpp/build-mutation/unit_tests ] || { echo "no mutation tree built, claim untestable"; exit 0; }
py=python/.venv/bin/python
[ -x "$py" ] || exit 2
report=cpp/build-mutation/probe-baseline.json
# ALETHEIA_LIB is unset for the sweep, not merely left alone: with it set the
# integration suite's library lookup returns before it reads the repository
# root, and the two mutants of that read go uncovered, so the same tree scores
# differently for a developer who has sourced the environment script.
(cd cpp/build-mutation &&
    env -u ALETHEIA_LIB ALETHEIA_REPO_ROOT="$OLDPWD" mull-runner-23 ./unit_tests \
        --report-name=probe-baseline --reporters=Elements > /dev/null 2>&1) || {
    echo "the sweep did not run"
    exit 1
}
"$py" - "$report" <<'PY'
import collections
import json
import sys

import yaml

report = json.load(open(sys.argv[1], encoding="utf-8"))
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
bad = {k: (baseline.get(k), v) for k, v in observed.items() if baseline.get(k) != v}
for key, (was, now) in bad.items():
    print(f"{key}: recorded {was}, a sweep gives {now}")
sys.exit(1 if bad else 0)
PY
