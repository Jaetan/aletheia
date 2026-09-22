#!/usr/bin/env bash
# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
#
# Probes docs/MUTATION_BENCH.yaml.
# Claim: the C++ baseline's kill routes record a run exactly. Sweeping the two
# configured trees under the order the lane pins, and reading each mutant's
# route the way the lane does, gives every route the recorded count, and the
# routes add up to the recorded total. There is no tolerance: Catch2 shuffles
# its cases by default, which moved the fault route between 93 and 101 across
# six orders of one tree, and the lane pins the order precisely so that the
# census is a measurement rather than one sample of that shuffle. Under the
# pinned order alone one mutant still moved between the test and the fault
# route, a skipped lookup guard reading a string past a map's end; the trees
# now compile under libstdc++'s debug mode, which ends such a read at the
# check, and two sweeps of each tree then moved nothing.
# A timeout is the exception, and it is not absorbed: one mutant runs close to
# the cap of ten times the unmutated baseline, so an oversubscribed machine
# times it out where an idle one reads the route it dies by. A sweep with any
# timeout is a census taken under load, which this reports as untestable
# rather than as a finding.
# Non-zero exit: a route differs from the recorded one, or the routes do not
# add up. Exits 0 with a note when Mull or either tree is absent, and 2 when
# the machine was too loaded to measure.
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
import sys
from pathlib import Path

import yaml

from tools.mutation_cpp import CppLeg, CppTree, cpp_kill_routes

baseline = yaml.safe_load(Path("docs/MUTATION_BENCH.yaml").read_text(encoding="utf-8"))
recorded = baseline["bindings"]["cpp"]["baseline"]
routes = recorded["kill_routes"]
# The trees swept whole above, which is how this census was recorded: a
# sliced run reads the same mutants through six reports instead of two.
observed = cpp_kill_routes(Path(sys.argv[1]), [CppLeg(tree) for tree in CppTree])
if observed is None:
    print("no census could be read from the sweeps")
    sys.exit(1)
if observed.get("timeout", 0):
    print(f"{observed['timeout']} mutant(s) timed out: the machine was loaded, census not comparable")
    sys.exit(2)
bad = False
for route in routes.keys() | observed.keys():
    if observed.get(route, 0) != routes.get(route, 0):
        print(f"{route}: {observed.get(route, 0)} observed, {routes.get(route, 0)} recorded")
        bad = True
if sum(observed.values()) != recorded["total_mutants"]:
    print(f"routes add up to {sum(observed.values())}, total recorded {recorded['total_mutants']}")
    bad = True
if not bad:
    print("PASS: " + ", ".join(f"{route} {count}" for route, count in observed.items()))
sys.exit(1 if bad else 0)
PY
