#!/usr/bin/env bash
# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
#
# Probes cpp/CMakeLists.txt.
# Claim: the mutation lane links the library statically, because the runner
# discovers mutants in the test executable and a shared library hides most of
# them. With the library shared the sweep found 14 mutants where the same
# sources yield 62 statically, and reported a clean score over a quarter of the
# surface, which is a gate that cannot fail on what it does not see.
# Non-zero exit: the mutation configuration no longer pins the static form, or
# the count it produces has fallen away from the recorded baseline.
set -u
cd "$(dirname "$0")/.." || exit 2
cmake=cpp/CMakeLists.txt

grep -q 'if(ALETHEIA_MUTATION)' "$cmake" || { echo "FAIL: no mutation branch on the library's link form"; exit 1; }
grep -q 'set(ALETHEIA_CPP_LINKAGE STATIC)' "$cmake" || {
    echo "FAIL: the mutation lane no longer pins the static link form"
    exit 1
}
grep -q 'add_library(aletheia-cpp ${ALETHEIA_CPP_LINKAGE}' "$cmake" || {
    echo "FAIL: the library does not take its link form from the mutation branch"
    exit 1
}

# The count itself, against the recorded baseline, when the lane is built.
report=cpp/build-mutation/probe-linkage.json
if [ -x cpp/build-mutation/unit_tests ] && command -v mull-runner-22 > /dev/null; then
    # The runner's exit code is not the signal here: it exits non-zero when a
    # mutant survives, and this probe asks how many mutants the lane can see
    # rather than how many it kills, which is the C++ baseline's question. A
    # sweep that genuinely could not run leaves no report, which is what is
    # checked instead.
    (cd cpp/build-mutation &&
        ALETHEIA_REPO_ROOT="$OLDPWD" mull-runner-22 ./unit_tests \
            --report-name=probe-linkage --reporters=Elements > /dev/null 2>&1) || true
    [ -s "$report" ] || {
        echo "FAIL: the sweep produced no report"
        exit 1
    }
    py=python/.venv/bin/python
    [ -x "$py" ] || py=python3
    "$py" - "$report" <<'PY'
import json
import sys

report = json.load(open(sys.argv[1], encoding="utf-8"))
total = sum(len(f.get("mutants", [])) for f in report["files"].values())
# The floor is the recorded baseline less a small margin, because the surface
# moves with the compiler; a collapse to a fraction is what this catches.
if total < 50:
    print(f"FAIL: the lane sees {total} mutants, far below the recorded baseline")
    raise SystemExit(1)
print(f"PASS: the lane sees {total} mutants")
PY
    exit $?
fi
echo "PASS: the mutation lane pins the static link form (lane not built, count not checked)"
