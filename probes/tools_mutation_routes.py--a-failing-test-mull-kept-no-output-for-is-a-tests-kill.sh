#!/usr/bin/env bash
# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
#
# Probes tools/mutation_routes.py.
# Claim: a mutant whose test failed by an assertion is read as a test's kill
# even where Mull kept none of the run's output. Mull reads each stream as
# UTF-8 and keeps nothing of one holding a byte that is not, so a failure
# report quoting raw input reaches the census as an empty stdout beside
# Catch2's failure exit, 42. Shown from a report row shaped as Mull writes
# that run, and, where clang-23 and Mull are installed, from a sweep, under
# the lane's own argv and environment, of a program whose mutant fails as a
# Catch2 test does, its failure report holding a byte that is not UTF-8. A
# run a signal ended, which Mull records with no exit status, is still read
# as a fault when nothing was kept.
# Non-zero exit: the failing run reads a route other than test, or the
# signal's one other than fault.
set -u
cd "$(dirname "$0")/.." || exit 2
py=python/.venv/bin/python
[ -x "$py" ] || exit 2
scratch=$(mktemp -d) || exit 2
trap 'rm -rf "$scratch"' EXIT
plugin=$HOME/.local/bin/mull-ir-frontend-23
sweep=no
if command -v clang++-23 > /dev/null && command -v mull-runner-23 > /dev/null && [ -x "$plugin" ]; then
    # The lane's runner starts the tree's unit_tests; this program stands in
    # for it, failing as Catch2 does once its mutant flips the comparison.
    cat > "$scratch/unit_tests.cpp" <<'CPP'
#include <cstdio>
static bool holds(int value) { return value == 1; }
int main() {
    if (holds(1)) return 0;
    std::fputs("unit_tests.cpp:4: FAILED:\n  REQUIRE( holds(1) )\nwith expansion:\n"
               "  input=[1\xe2\x82.5]\n\n", stdout);
    return 42;
}
CPP
    printf 'mutators:\n  - cxx_eq_to_ne\n' > "$scratch/mull.yml"
    mkdir "$scratch/report" || exit 2
    MULL_CONFIG="$scratch/mull.yml" clang++-23 -fpass-plugin="$plugin" -g -O0 -grecord-command-line \
        "$scratch/unit_tests.cpp" -o "$scratch/unit_tests" || exit 2
    sweep=yes
else
    echo "clang-23 or Mull not installed, the sweep is skipped and the recorded row read alone"
fi
"$py" - "$scratch" "$sweep" <<'PY'
import contextlib
import os
import shutil
import sqlite3
import subprocess
import sys
from pathlib import Path

from tools.mutation_cpp import (
    CPP_SWEEP_LOCALE,
    CppLeg,
    CppTree,
    SearchPath,
    SweepEnvironment,
    cpp_lane_command,
)
from tools.mutation_routes import lane_endings

scratch, sweep = Path(sys.argv[1]), sys.argv[2] == "yes"
recorded = scratch / "recorded.sqlite"
# Execution status 1 is a run that failed; the exit status is the process's
# own, and -1 where a signal ended it.
with contextlib.closing(sqlite3.connect(recorded)) as conn:
    conn.execute(
        "CREATE TABLE mutant (mutant_id TEXT, execution_status INT, exit_status INT,"
        " stdout TEXT, stderr TEXT)"
    )
    conn.executemany(
        "INSERT INTO mutant VALUES (?, ?, ?, ?, ?)",
        [("failed", 1, 42, "", ""), ("signalled", 1, -1, "", "")],
    )
    conn.commit()
wanted = {"failed": "test", "signalled": "fault"}
bad = [f"recorded {mutant}: read {ending.route}, stands for {wanted[mutant]}"
       for mutant, ending in lane_endings(recorded).items() if ending.route != wanted[mutant]]
if sweep:
    leg = CppLeg(CppTree.PLAIN)
    runner = shutil.which("mull-runner-23")
    if runner is None:
        sys.exit(2)
    environment = SweepEnvironment(
        SearchPath(os.environ.get("PATH") or os.defpath), CPP_SWEEP_LOCALE, scratch, scratch,
        scratch / "mull.yml",
    )
    ran = subprocess.run(
        cpp_lane_command(runner, scratch, scratch / "report", leg),
        cwd=scratch, env=environment.variables(), capture_output=True, text=True, check=False,
    )
    swept = scratch / "report" / f"{leg.report_name}.sqlite"
    if ran.returncode != 0 or not swept.is_file():
        print(ran.stdout + ran.stderr)
        sys.exit(2)
    with contextlib.closing(sqlite3.connect(swept)) as conn:
        kept = conn.execute("SELECT exit_status, length(stdout) FROM mutant").fetchall()
    print(f"the sweep's runs, as (exit status, stdout characters Mull kept): {kept}")
    endings = lane_endings(swept)
    if not endings:
        bad.append("the sweep recorded no mutant")
    bad += [f"swept {mutant}: read {ending.route}, stands for test"
            for mutant, ending in endings.items() if ending.route != "test"]
for line in bad:
    print(line)
sys.exit(1 if bad else 0)
PY
