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
# instrument the tree is read with. Each leg, the unsliced tree and every
# slice, is read where the lane builds it, by a dry run of the lane's own
# command in the lane's environment and directory, the reports in scratch;
# the trees are only read. Legs built from different sources need not agree,
# so a leg whose tree is not built, was built under another configuration
# than the lane gives it now, or is older than a tracked C++ source is
# refused, and the lane rebuilds it.
# Non-zero exit: a dry run writes no report, a slice shares an identifier
# with another, or the union is not the unsliced census. Exits 2 when a
# leg's tree is absent or stale, and 0 with a note when Mull, clang-23,
# clang++-23 or the plugin is absent.
set -u
cd "$(dirname "$0")/.." || exit 2
command -v mull-runner-23 > /dev/null || { echo "Mull not installed, claim untestable"; exit 0; }
command -v clang-23 > /dev/null || { echo "clang-23 not installed, claim untestable"; exit 0; }
command -v clang++-23 > /dev/null || { echo "clang++-23 not installed, claim untestable"; exit 0; }
[ -x "$HOME/.local/bin/mull-ir-frontend-23" ] || { echo "plugin not installed, claim untestable"; exit 0; }
py=python/.venv/bin/python
[ -x "$py" ] || exit 2

exec "$py" - <<'PY'
import itertools
import json
import subprocess
import sys
import tempfile
from pathlib import Path

from tools.mutation_cpp import CPP_TEST_TARGET
from tools.mutation_cpp_config import built_under_config, leg_files
from tools.mutation_cpp_legs import CppLeg, CppTree
from tools.mutation_cpp_slices import CPP_SLICES
from tools.mutation_cpp_dry_run import dry_run_report, leg_build_dir

sources = subprocess.run(
    ["git", "ls-files", "-z", "--", "cpp/src", "cpp/include", "cpp/tests", "cpp/CMakeLists.txt"],
    capture_output=True, text=True, check=True,
).stdout.split("\0")
newest = max((Path(source) for source in sources if source), key=lambda source: source.stat().st_mtime)


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
        binary = build_dir / CPP_TEST_TARGET
        if not binary.is_file():
            print(f"the {leg} tree is not built at {build_dir}; build it with the lane")
            sys.exit(2)
        if not built_under_config(leg, build_dir):
            print(f"the {leg} tree was built under another configuration than the lane gives it; rebuild it")
            sys.exit(2)
        if binary.stat().st_mtime < newest.stat().st_mtime:
            print(f"the {leg} tree is older than {newest}; rebuild it with the lane")
            sys.exit(2)
        if leg.slice_no is not None:
            _, held_out = leg_files(leg)
            sys.stderr.write(f"slice {leg.slice_no}: {len(held_out)} of the domain's files held out\n")
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
