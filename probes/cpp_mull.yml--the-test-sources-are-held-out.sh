#!/usr/bin/env bash
# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
#
# Probes cpp/mull.yml.
# Claim: the test sources are held out of the mutation surface and the library
# headers they instantiate are not. A mutant in a test measures the harness,
# and one in a fixture's write loop ran until the runner killed the process,
# leaving a multi-gigabyte file behind each time; a library header compiled
# only through a test, such as the loaders' dispatcher through its unit test,
# is library code and keeps its mutants. The leak tree is read through a dry
# run of the lane's own command, in the lane's environment and directory, its
# report in scratch. Non-zero exit: the dry run lists a mutant under
# cpp/tests, or none in cpp/src/detail/loader_utils.hpp, or writes no report.
# Exits 0 with a note when Mull or the mutation tree is not available, since
# the claim is untestable then.
set -u
cd "$(dirname "$0")/.." || exit 2
py=python/.venv/bin/python
[ -x "$py" ] || exit 2

exec "$py" - <<'PY'
import json
import os
import shutil
import sys
import tempfile
from pathlib import Path

from tools.mutation_cpp_legs import CppLeg, CppTree
from tools.mutation_sweep_cache import MULL_RUNNER, dry_run_report, tree_binary

if shutil.which(MULL_RUNNER) is None:
    print("Mull not installed, claim untestable")
    sys.exit(0)
if not os.access(tree_binary(CppTree.LEAK), os.X_OK):
    print("no mutation tree built, claim untestable")
    sys.exit(0)
with tempfile.TemporaryDirectory(prefix="dry-run-") as scratch:
    report = dry_run_report(CppLeg(CppTree.LEAK), Path(scratch))
    if isinstance(report, str):
        print(report)
        sys.exit(1)
    files = json.loads(report.read_text(encoding="utf-8"))["files"]

in_tests = {path for path, entry in files.items() if "/cpp/tests/" in path and entry.get("mutants")}
header = sum(
    len(entry.get("mutants", []))
    for path, entry in files.items()
    if path.endswith("/cpp/src/detail/loader_utils.hpp")
)
bad = False
if in_tests:
    print("mutants listed under cpp/tests: " + ", ".join(sorted(in_tests)))
    bad = True
if header == 0:
    print("no mutant in cpp/src/detail/loader_utils.hpp")
    bad = True
sys.exit(1 if bad else 0)
PY
