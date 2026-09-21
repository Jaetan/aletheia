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
# route, a skipped lookup guard reading a string past a map's end; both trees
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
[ -x cpp/build-mutation/unit_tests ] && [ -x cpp/build-mutation-plain/unit_tests ] ||
    { echo "the mutation trees are not both built, claim untestable"; exit 0; }
py=python/.venv/bin/python
[ -x "$py" ] || exit 2
dir=$(mktemp -d) || exit 2
trap 'rm -rf "$dir"' EXIT
# The lane's environment: the repository root for the integration suite, and
# no ALETHEIA_LIB, so the library lookup reads the root as the lane's does.
# The runner's argv is the lane's own, built by tools/mutation_cpp.py, so the
# cap per mutant and the pinned order have one owner; only where the reports
# land is this probe's.
for lane in leak plain; do
    argv=$("$py" -c 'import shlex, sys
from pathlib import Path
from tools.mutation_cpp import CppLeg, CppTree, cpp_lane_command
leg = CppLeg(CppTree(sys.argv[2]))
print(shlex.join(cpp_lane_command("mull-runner-23", Path("cpp", leg.directory).resolve(), Path(sys.argv[1]), leg)))' "$dir" "$lane") || exit 2
    (cd cpp && unset ALETHEIA_LIB && ALETHEIA_REPO_ROOT="$OLDPWD" eval "$argv" > /dev/null 2>&1) || true
    [ -f "$dir/cpp-mull-$lane.sqlite" ] || { echo "the $lane tree's sweep wrote no SQLite report"; exit 1; }
done
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
