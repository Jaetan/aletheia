#!/usr/bin/env bash
# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
#
# Probes cpp/CMakeLists.txt.
# Claim: the mutation lane links the library statically, because the runner
# discovers mutants in the test executable and a shared library hides most of
# them. With the library shared the sweep found 14 mutants where the same
# sources yield 62 statically, and reported a clean score over a quarter of the
# surface, which is a gate that cannot fail on what it does not see. The count
# is read through a dry run of the leak tree with the lane's own command, in
# the lane's environment and directory, its report in scratch: a dry run lists
# every mutant the binary carries without running one.
# Non-zero exit: the mutation configuration no longer pins the static form,
# the census records no count for the leak tree, the leak tree carries fewer
# mutants than the census records for it, or the dry run writes no report.
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

# The count itself, against the recorded census, when the lane is built.
py=python/.venv/bin/python
[ -x "$py" ] || exit 2
exec "$py" - <<'PY'
import json
import os
import shutil
import sys
import tempfile
from pathlib import Path

from tools.mutation_cpp import recorded_total_mutants
from tools.mutation_cpp_legs import CppLeg, CppTree
from tools.mutation_sweep_cache import MULL_RUNNER, dry_run_report, tree_binary

if shutil.which(MULL_RUNNER) is None or not os.access(tree_binary(CppTree.LEAK), os.X_OK):
    print("PASS: the mutation lane pins the static link form (lane not built, count not checked)")
    sys.exit(0)
recorded = recorded_total_mutants(CppTree.LEAK)
if recorded is None:
    print("FAIL: the census records no mutant count for the leak tree")
    sys.exit(1)
with tempfile.TemporaryDirectory(prefix="dry-run-") as scratch:
    report = dry_run_report(CppLeg(CppTree.LEAK), Path(scratch))
    if isinstance(report, str):
        print(f"FAIL: {report}")
        sys.exit(1)
    files = json.loads(report.read_text(encoding="utf-8"))["files"]
total = sum(len(entry.get("mutants", [])) for entry in files.values())
if total < recorded:
    print(f"FAIL: the lane sees {total} mutants, the census records {recorded} for the leak tree")
    sys.exit(1)
print(f"PASS: the lane sees {total} mutants, the census records {recorded}")
PY
