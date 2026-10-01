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
# are the same with the flag and without it. This sweeps every tree the lane
# sweeps once more, with the lane's argv less that flag, and compares each
# mutant's ending with the kept sweep, which carries it.
# A timeout is not compared: the cap per mutant is a wall clock, so a sweep
# with one was taken under load.
# Non-zero exit: a mutant's ending differs between the two sweeps, or they
# sweep different mutants. Exits 0 with a note when Mull or a tree is absent,
# and 2 when no kept sweep could be had or a timeout shows a loaded machine.
set -u
cd "$(dirname "$0")/.." || exit 2
command -v mull-runner-23 > /dev/null || { echo "Mull not installed, claim untestable"; exit 0; }
py=python/.venv/bin/python
[ -x "$py" ] || exit 2
dir=$("$py" -m tools.mutation_sweep_cache) || {
    echo "no sweep of the mutation trees could be had"
    exit 2
}

exec "$py" - "$dir" <<'PY'
import subprocess
import sys
import tempfile
from pathlib import Path

from aletheia.common_types import Prose
from tools.cpp_scratch import reap_dead_scratch_dirs
from tools.mutation_cpp import cpp_lane_command, cpp_sweep_directory, cpp_sweep_environment
from tools.mutation_cpp_legs import CppLeg, CppTree
from tools.mutation_routes import lane_endings
from tools.mutation_sweep_cache import MULL_RUNNER, leg_build_dir, polite

kept = Path(sys.argv[1])
moved: list[Prose] = []
compared = 0
with tempfile.TemporaryDirectory(prefix="abort-") as scratch:
    for tree in CppTree:
        leg = CppLeg(tree)
        build_dir = leg_build_dir(leg)
        report_dir = Path(scratch) / tree.value
        report_dir.mkdir()
        argv = cpp_lane_command(MULL_RUNNER, build_dir, report_dir, leg)
        if "--abort" not in argv[argv.index("--") :]:
            print("the lane's argv carries no --abort, so there is nothing to compare")
            sys.exit(1)
        argv.remove("--abort")
        _ = subprocess.run(
            polite(argv),
            cwd=cpp_sweep_directory(),
            env=cpp_sweep_environment(leg, build_dir).variables(),
            capture_output=True,
            check=False,
        )
        _ = reap_dead_scratch_dirs()
        whole = report_dir / f"{leg.report_name}.sqlite"
        if not whole.is_file():
            print(f"the {tree.value} sweep without --abort wrote no report")
            sys.exit(1)
        with_flag = lane_endings(kept / f"{leg.report_name}.sqlite")
        without = lane_endings(whole)
        if any(ending.route == "timeout" for ending in (*with_flag.values(), *without.values())):
            print(f"the {tree.value} tree timed out a mutant: the machine was loaded, not comparable")
            sys.exit(2)
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
