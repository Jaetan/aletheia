#!/usr/bin/env bash
# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
#
# Probes tools/mutation_cpp_slices.py.
# Claim: slicing the surface by file changes which mutants a build carries and
# nothing about their identity, so the slices of a tree are disjoint and union
# to exactly the census that tree carries unsliced. Everything the sliced lane
# does rests on this: the merge unions a tree's slices before intersecting the
# trees, and a mutant one slice killed is the same mutant another slice would
# have named. Two ways it could fail, neither visible from reading: Mull names a
# mutant partly by an ordinal among its function's mutants of the same mutator
# and range, so a filter that reached inside a file would renumber what it kept;
# and the patterns holding the other slices out are written by Python and read
# by the plugin's own regular-expression engine, so an escape either side spells
# differently is a file not held out at all.
# The plain tree alone, because the claim is about slicing and not about the
# instrument the tree is read with, and a tree costs a build. Each leg, the
# unsliced tree and every slice, is configured, built and read as the lane
# does it: its configuration put in place by the lane's own code, which also
# discards a tree built under other content, the lane's own build, and a dry
# run of the lane's own command in the lane's environment and directory, the
# reports and build logs in scratch.
# Non-zero exit: a leg does not build, a dry run writes no report, a slice
# shares an identifier with another, or the union is not the unsliced census.
# Exits 0 with a note when Mull, clang-23, clang++-23, the plugin or cmake is
# absent.
set -u
cd "$(dirname "$0")/.." || exit 2
command -v mull-runner-23 > /dev/null || { echo "Mull not installed, claim untestable"; exit 0; }
command -v clang-23 > /dev/null || { echo "clang-23 not installed, claim untestable"; exit 0; }
command -v clang++-23 > /dev/null || { echo "clang++-23 not installed, claim untestable"; exit 0; }
[ -x "$HOME/.local/bin/mull-ir-frontend-23" ] || { echo "plugin not installed, claim untestable"; exit 0; }
py=python/.venv/bin/python
[ -x "$py" ] || exit 2

exec "$py" - <<'PY'
import contextlib
import itertools
import json
import shutil
import sys
import tempfile
from pathlib import Path

from tools.mutation_cpp import LegPaths, build_cpp_mutation_tree, cpp_sweep_directory
from tools.mutation_cpp_config import leg_config, leg_files
from tools.mutation_cpp_legs import CppLeg, CppTree
from tools.mutation_cpp_slices import CPP_SLICES
from tools.mutation_sweep_cache import dry_run_report, leg_build_dir

cmake = shutil.which("cmake")
if cmake is None:
    print("cmake not installed, claim untestable")
    sys.exit(0)


def identifiers(report: Path) -> list[str]:
    """Every mutant identifier one dry run reported, in the order it reported them."""
    files = json.loads(report.read_text(encoding="utf-8"))["files"]
    return [str(mutant["id"]) for entry in files.values() for mutant in entry["mutants"]]


unsliced = CppLeg(CppTree.PLAIN)
slices = [CppLeg(CppTree.PLAIN, number) for number in range(1, CPP_SLICES + 1)]
found = {}
with tempfile.TemporaryDirectory(prefix="slices-") as scratch:
    for leg in (unsliced, *slices):
        build_dir = leg_build_dir(leg)
        config = leg_config(leg, build_dir)
        if leg.slice_no is not None:
            _, held_out = leg_files(leg)
            sys.stderr.write(f"slice {leg.slice_no}: {len(held_out)} of the domain's files held out\n")
        log = Path(scratch) / f"{leg}.log"
        with log.open("w", encoding="utf-8") as sink, contextlib.redirect_stderr(sink):
            paths = LegPaths(cpp_sweep_directory(), build_dir, Path(scratch), config)
            built = build_cpp_mutation_tree(cmake, paths, leg)
        if not isinstance(built, str):
            print(f"the {leg} leg did not build: {built.error}")
            print(log.read_text(encoding="utf-8")[-2000:])
            sys.exit(1)
        report = dry_run_report(leg, Path(scratch))
        if isinstance(report, str):
            print(report)
            sys.exit(1)
        found[leg] = identifiers(report)

whole = found[unsliced]
parts = {leg.slice_no: found[leg] for leg in slices}
status = 0
for left, right in itertools.combinations(parts, 2):
    shared = set(parts[left]) & set(parts[right])
    if shared:
        print(f"slices {left} and {right} share {len(shared)} identifiers, e.g. {sorted(shared)[0]}")
        status = 1
union = [mutant for part in parts.values() for mutant in part]
if len(union) != len(set(union)):
    print(f"the union repeats an identifier: {len(union)} mutants, {len(set(union))} distinct")
    status = 1
for missing in sorted(set(whole) - set(union))[:3]:
    print(f"the unsliced tree carries {missing} and no slice does")
    status = 1
for extra in sorted(set(union) - set(whole))[:3]:
    print(f"a slice carries {extra} and the unsliced tree does not")
    status = 1
sizes = ", ".join(str(len(part)) for _, part in sorted(parts.items()))
if status == 0:
    print(f"PASS: slices of {sizes} union to the unsliced tree's {len(whole)} mutants, disjoint")
sys.exit(status)
PY
