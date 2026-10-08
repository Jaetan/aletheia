#!/usr/bin/env bash
# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
#
# Probes cpp/mull.yml.
# Claim: the test double under cpp/src/detail is held out of the mutation
# surface. Only the tests include it, so a mutant in it measures the harness
# rather than the library, the reason the test sources are held out; the
# library's other detail sources keep their mutants. The leak tree is read
# through a dry run of the lane's own command, in the lane's environment and
# directory, its report in scratch. Non-zero exit: the dry run lists a mutant
# in cpp/src/detail/mock_backend.hpp, or none in cpp/src/detail/ffi_logic.cpp,
# or writes no report. Exits 0 with a note when Mull or the mutation tree is
# not available, since the claim is untestable then.
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
from tools.mutation_cpp_dry_run import MULL_RUNNER, dry_run_report, tree_binary

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


def mutants(suffix):
    return sum(len(e.get("mutants", [])) for p, e in files.items() if p.endswith(suffix))


bad = False
if mutants("/cpp/src/detail/mock_backend.hpp"):
    print("mutants listed in cpp/src/detail/mock_backend.hpp")
    bad = True
if mutants("/cpp/src/detail/ffi_logic.cpp") == 0:
    print("no mutant in cpp/src/detail/ffi_logic.cpp")
    bad = True
sys.exit(1 if bad else 0)
PY
