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
# instrument the tree is read with, and a tree costs a build.
# Non-zero exit: a slice shares an identifier with another, or the union is not
# the unsliced census. Exits 0 with a note when Mull or clang-23 is absent.
set -u
cd "$(dirname "$0")/.." || exit 2
command -v mull-runner-23 > /dev/null || { echo "Mull not installed, claim untestable"; exit 0; }
command -v clang++-23 > /dev/null || { echo "clang++-23 not installed, claim untestable"; exit 0; }
[ -x "$HOME/.local/bin/mull-ir-frontend-23" ] || { echo "plugin not installed, claim untestable"; exit 0; }
py=python/.venv/bin/python
[ -x "$py" ] || exit 2

reports=$(mktemp -d) || exit 2
trap 'rm -rf "$reports"' EXIT
root=$PWD
slices=$("$py" -c 'from tools.mutation_cpp_slices import CPP_SLICES; print(CPP_SLICES)') || exit 2

# Each slice's configuration, put in place by the lane's own code, so this
# reads what a leg builds under and not a second spelling of it. That call is
# also what discards a tree whose objects were built under other content.
"$py" - <<'PYEOF' || exit 1
import sys
from pathlib import Path

from tools.mutation_cpp import CppLeg, CppTree, leg_config, leg_files
from tools.mutation_cpp_slices import CPP_SLICES

root = Path.cwd()
for number in range(1, CPP_SLICES + 1):
    leg = CppLeg(CppTree.PLAIN, number)
    _ = leg_config(leg, root / "cpp" / leg.directory)
    _, held_out = leg_files(leg)
    sys.stderr.write(f"slice {number}: {len(held_out)} of the domain's files held out\n")
PYEOF

# The unsliced tree is the oracle; the slices are what is checked against it.
build() { # <directory> <configuration>
    cmake -S cpp -B "cpp/$1" -DALETHEIA_MUTATION=ON "-DALETHEIA_MULL_CONFIG=$2" \
        -DCMAKE_C_COMPILER=clang-23 -DCMAKE_CXX_COMPILER=clang++-23 > "$reports/$1.log" 2>&1 &&
        cmake --build "cpp/$1" --target unit_tests --parallel 8 >> "$reports/$1.log" 2>&1
}
census() { # <directory> <configuration> <report name>
    env -u ALETHEIA_LIB ALETHEIA_REPO_ROOT="$root" MULL_CONFIG="$2" \
        mull-runner-23 "./cpp/$1/unit_tests" --dry-run --reporters=Elements \
        --report-dir="$reports" --report-name="$3" -- --order decl > /dev/null 2>&1
}
build build-mutation-plain "$root/cpp/mull.yml" ||
    { echo "the unsliced tree did not build, see $reports"; cp "$reports"/*.log /tmp 2>/dev/null; exit 1; }
census build-mutation-plain "$root/cpp/mull.yml" whole ||
    { echo "the unsliced tree's dry run failed"; exit 1; }
number=1
while [ "$number" -le "$slices" ]; do
    config="$root/cpp/build-mutation-plain-$number/mull-slice.yml"
    build "build-mutation-plain-$number" "$config" ||
        { echo "slice $number did not build"; exit 1; }
    census "build-mutation-plain-$number" "$config" "slice-$number" ||
        { echo "slice $number's dry run failed"; exit 1; }
    number=$((number + 1))
done

"$py" - "$reports" "$slices" <<'PYEOF'
import itertools
import json
import sys

reports, slices = sys.argv[1], int(sys.argv[2])


def identifiers(name: str) -> list[str]:
    """Every mutant identifier one dry run reported, in the order it reported them."""
    with open(f"{reports}/{name}.json", encoding="utf-8") as report:
        files = json.load(report)["files"]
    return [str(mutant["id"]) for entry in files.values() for mutant in entry["mutants"]]


whole = identifiers("whole")
parts = {number: identifiers(f"slice-{number}") for number in range(1, slices + 1)}
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
PYEOF
