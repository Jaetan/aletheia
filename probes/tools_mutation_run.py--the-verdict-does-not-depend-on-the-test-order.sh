#!/usr/bin/env bash
# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
#
# Probes tools/mutation_run.py, the lane that sweeps the C++ mutants, and the
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
# then the mutant verdicts under three orders, which sweeps the tree three
# times and costs about ten minutes.
# Non-zero exit: the suite fails under some order, or a mutant's verdict
# depends on it. Exits 0 with a note when Mull or the tree is absent, the
# claim being untestable then.
set -u
cd "$(dirname "$0")/.." || exit 2
tree=cpp/build-mutation-plain
[ -x "$tree/unit_tests" ] || { echo "the plain mutation tree is not built, claim untestable"; exit 0; }

# Stage one: the suite itself, unmutated, under orders that share no structure.
# The lane's environment, since this binary folds in the tests that read the
# repository root, and the library lookup must reach it the way the lane does.
suite() { (cd "$tree" && env -u ALETHEIA_LIB ALETHEIA_REPO_ROOT="$OLDPWD" \
    ./unit_tests "$@" > /dev/null 2>&1); }
for order in decl lex; do
    suite --order "$order" || { echo "the unmutated suite fails under --order $order"; exit 1; }
done
for seed in 7 8191; do
    suite --order rand --rng-seed "$seed" ||
        { echo "the unmutated suite fails under --order rand --rng-seed $seed"; exit 1; }
done

command -v mull-runner-23 > /dev/null || { echo "Mull not installed, the mutant half is untestable"; exit 0; }
py=python/.venv/bin/python
[ -x "$py" ] || exit 2
dir=$(mktemp -d) || exit 2
trap 'rm -rf "$dir"' EXIT

sweep() { # report name, then the binary's own argv
    local name=$1; shift
    (cd "$tree" && env -u ALETHEIA_LIB ALETHEIA_REPO_ROOT="$OLDPWD" \
        mull-runner-23 ./unit_tests --report-name="$name" --report-dir="$dir" \
        --reporters=SQLite "$@" > /dev/null 2>&1) || true
    [ -f "$dir/$name.sqlite" ] || { echo "the sweep under $name wrote no report"; return 1; }
}
sweep decl -- --order decl || exit 1
sweep lex -- --order lex || exit 1
sweep rand -- --order rand --rng-seed 4919 || exit 1

"$py" - "$dir" <<'PY'
import sys
from pathlib import Path

from tools.mutation_routes import lane_routes

runs = {p.stem: lane_routes(p) for p in sorted(Path(sys.argv[1]).glob("*.sqlite"))}
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
