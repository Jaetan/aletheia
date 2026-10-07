#!/usr/bin/env bash
# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
#
# Probes tools/mutation_cpp.py, the lane that sweeps the C++ mutants.
# Claim: ending a mutant's run at its first failing assertion moves no
# mutant's ending. The lane hands the test binary Catch2's --abort, so a run
# stops at the first assertion that fails instead of going through the rest of
# the suite. The kill-route census reads a run with any failing assertion as
# the test's kill, whatever ended the process after it, and a run with none
# goes through the whole suite either way, so each mutant's route, the check
# or the address class it names where it has one, and the verdict with them,
# are the same with the flag and without it. Two kept sweeps of every tree
# (tools/mutation_sweep_cache.py) are compared mutant by mutant: the lane's,
# and one under the lane's argv less that flag, each swept only where none of
# today's trees is kept.
# A timeout is not compared: the cap per mutant is a backstop, so a sweep in
# which it fired is a disturbed run, and the mutant it ended a hang to remove.
# Non-zero exit: a mutant's ending differs between the two sweeps, they sweep
# different mutants, or a mutant timed out. Exits 0 with a note when Mull is
# absent, and 2 when no kept sweep could be had, an unbuilt tree among the
# reasons the cache gives.
set -u
cd "$(dirname "$0")/.." || exit 2
command -v mull-runner-23 > /dev/null || { echo "Mull not installed, claim untestable"; exit 0; }
py=python/.venv/bin/python
[ -x "$py" ] || exit 2

exec "$py" - <<'PY'
import sys
from pathlib import Path

from aletheia.common_types import Prose
from tools.mutation_cpp import CppRun
from tools.mutation_cpp_legs import CppLeg, CppTree
from tools.mutation_routes import lane_endings
from tools.mutation_sweep_cache import CppVariant, sweep_directory

kept = sweep_directory()
unaborted = sweep_directory(variant=CppVariant(tuple(CppTree), CppRun(abort=False)))
if not isinstance(kept, Path) or not isinstance(unaborted, Path):
    print(f"no sweep of the mutation trees could be had: {kept}; {unaborted}")
    sys.exit(2)
moved: list[Prose] = []
compared = 0
for tree in CppTree:
    report = f"{CppLeg(tree).report_name}.sqlite"
    with_flag = lane_endings(kept / report)
    without = lane_endings(unaborted / report)
    if any(ending.route == "timeout" for ending in (*with_flag.values(), *without.values())):
        print(f"the {tree.value} tree timed out a mutant: a disturbed run, not comparable")
        sys.exit(1)
    if with_flag.keys() != without.keys():
        print(f"the {tree.value} sweeps with and without --abort carry different mutants")
        sys.exit(1)
    compared += len(with_flag)
    moved += [
        Prose(f"  {tree.value} {mutant}: {without[mutant]} without, {with_flag[mutant]} with")
        for mutant in sorted(with_flag)
        if with_flag[mutant] != without[mutant]
    ]
if moved:
    print(f"{len(moved)} mutants whose ending moves with --abort:")
    print("\n".join(moved[:10]))
    sys.exit(1)
print(f"PASS: {compared} mutants, one ending each with and without --abort")
PY
