#!/usr/bin/env bash
# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
#
# Probes tools/mutation_cpp.py, the lane that sweeps the C++ mutants, and the
# suite it sweeps.
# Claim: whatever is mutated, every permutation of the tests gives the same
# verdict for every mutant. The lane pins the order so that the census it
# records is a measurement rather than one sample of Catch2's shuffle, and
# this holds the property that pinning could otherwise hide: a mutant whose
# killed-or-survived answer moves with the order is inter-test coupling, a
# defect of the tests. The route may legitimately differ, since a fault ends
# the process and the order decides which test reports before it stops, so
# only the verdict is compared.
# Two stages: the unmutated suite under several orders, which costs seconds,
# then the mutant verdicts under three orders, read from kept sweeps of the
# plain tree (tools/mutation_sweep_cache.py): the lane's own for the order it
# pins, and one under the lane's argv with only the order varied for each
# other, each swept only where none of today's trees is kept. Both stages run
# the plain tree as the lane does, in the lane's environment and directory.
# Non-zero exit: the suite fails under some order, or a mutant's verdict
# depends on it. Exits 0 with a note when Mull or the tree is absent, the
# claim being untestable then.
set -u
cd "$(dirname "$0")/.." || exit 2
py=python/.venv/bin/python
[ -x "$py" ] || exit 2

exec "$py" - <<'PY'
import os
import shutil
import subprocess
import sys
from pathlib import Path

from tools.mutation_cpp import CaseOrder, CppRun, RngSeed, cpp_sweep_directory, cpp_sweep_environment
from tools.mutation_cpp_legs import CppLeg, CppTree
from tools.mutation_routes import lane_routes
from tools.mutation_sweep_cache import (
    MULL_RUNNER,
    CppVariant,
    sweep_directory,
    tree_binary,
    tree_build_dir,
)

leg = CppLeg(CppTree.PLAIN)
build_dir = tree_build_dir(leg.tree)
binary = tree_binary(leg.tree)
if not os.access(binary, os.X_OK):
    print("the plain mutation tree is not built, claim untestable")
    sys.exit(0)
env = cpp_sweep_environment(leg, build_dir).variables()

# Stage one: the suite itself, unmutated, under orders that share no structure.
for order in (["decl"], ["lex"], ["rand", "--rng-seed", "7"], ["rand", "--rng-seed", "8191"]):
    suite = subprocess.run(
        [str(binary), "--order", *order], cwd=cpp_sweep_directory(), env=env, capture_output=True, check=False
    )
    if suite.returncode != 0:
        print(f"the unmutated suite fails under --order {' '.join(order)}")
        sys.exit(1)

if shutil.which(MULL_RUNNER) is None:
    print("Mull not installed, the mutant half is untestable")
    sys.exit(0)

# Stage two: the mutants, one kept sweep per order.
runs = {}
for name, run in (
    ("decl", None),
    ("lex", CppRun(order=CaseOrder("lex"))),
    ("rand", CppRun(order=CaseOrder("rand", RngSeed(4919)))),
):
    kept = sweep_directory() if run is None else sweep_directory(variant=CppVariant((leg.tree,), run))
    if not isinstance(kept, Path):
        print(f"no sweep under {name} could be had: {kept}")
        sys.exit(1)
    runs[name] = lane_routes(kept / f"{leg.report_name}.sqlite")

verdicts = {name: {m: r == "survived" for m, r in routes.items()} for name, routes in runs.items()}
names = sorted(verdicts)
base = names[0]
disagree: set[str] = set()
for other in names[1:]:
    if verdicts[base].keys() != verdicts[other].keys():
        print(f"{base} and {other} do not sweep the same mutants")
        sys.exit(1)
    disagree |= {m for m in verdicts[base] if verdicts[base][m] != verdicts[other][m]}
if disagree:
    print(f"{len(disagree)} mutants whose verdict depends on the test order:")
    for mutant in sorted(disagree)[:10]:
        print("  " + mutant + ": " + ", ".join(f"{n}={runs[n][mutant]}" for n in names))
    sys.exit(1)
print(f"PASS: {len(verdicts[base])} mutants, one verdict each across {len(names)} orders")
PY
