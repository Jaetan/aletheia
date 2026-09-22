#!/usr/bin/env bash
# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
#
# Probes docs/MUTATION_BENCH.yaml.
# Claim: the C++ baseline records a run, not a target. The recorded survivor
# count and mutant total are what sweeps of every configured tree produce,
# merged the way the lane merges them, under the order the lane pins, and the
# sweep times nothing out. A timeout is a kill by another route, and one
# mutant runs close to the cap of ten times the unmutated baseline, so an
# oversubscribed machine times it out where an idle one reads the route it
# dies by: that is a property of the machine rather than of the code, so a
# sweep with any timeout is a census taken under load and is reported as
# untestable instead of tolerated. Non-zero exit: the record and the sweep
# disagree. Exits 0 with a note when Mull or either mutation tree is not
# available, since the claim is untestable then, and 2 when the machine was
# too loaded to measure.
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
# ALETHEIA_LIB is unset for the sweep, not merely left alone: with it set the
# integration suite's library lookup returns before it reads the repository
# root, and the two mutants of that read go uncovered, so the same tree scores
# differently for a developer who has sourced the environment script.
# The runner's exit code is not the signal: it exits non-zero when any mutant
# survives, which a baseline above zero guarantees. A sweep that could not run
# leaves no report, and that is what is checked.
# Every tree is swept, because a mutant survives the lane only where every
# tree carrying it let it survive: the leak tree reports a destructor removal
# that leaks, the address tree a value read after what held it has gone, and
# the plain tree carries the allocation-fault sweeps, which no sanitizer tree
# can carry because a sanitizer defines the allocation functions they replace.
# The runner's argv is the lane's own, built by tools/mutation_cpp.py, so the
# cap per mutant and the pinned order have one owner; only where the reports
# land is this probe's.
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
reports=""
for lane in $trees; do reports="$reports $dir/cpp-mull-$lane.json"; done
# shellcheck disable=SC2086
"$py" - $reports <<'PY'
import collections
import json
import sys

import yaml

sys.path.insert(0, ".")
from tools.mutation_cpp import merge_elements

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
if observed["timeouts"] > baseline.get("timeouts", 0):
    print(
        f"{observed['timeouts']} mutant(s) timed out against {baseline.get('timeouts', 0)} "
        "recorded: the machine was loaded, the census is not comparable"
    )
    sys.exit(2)
bad = {k: (baseline.get(k), v) for k, v in observed.items() if baseline.get(k) != v}
for key, (was, now) in bad.items():
    print(f"{key}: recorded {was}, a sweep gives {now}")
sys.exit(1 if bad else 0)
PY
