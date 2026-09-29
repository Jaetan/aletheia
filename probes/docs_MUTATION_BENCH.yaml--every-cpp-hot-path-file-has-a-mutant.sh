#!/usr/bin/env bash
# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
#
# Probes docs/MUTATION_BENCH.yaml.
# Claim: every file the C++ hot_path list names is on the mutation surface,
# which means a dry run over the mutation binary lists at least one mutant in
# it. A listed file that no suite linked into the mutation binary reaches, or
# whose mutants the plugin's junk detector drops, is a surface the lane does
# not have. The leak tree is read through a dry run of the lane's own
# command, in the lane's environment and directory, its report in scratch.
# Non-zero exit: a listed file has no mutant in the dry run, or the dry run
# writes no report. Exits 0 with a note when Mull or the mutation tree is not
# available, since the claim is untestable then.
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

import yaml

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

counts = {path: len(entry.get("mutants", [])) for path, entry in files.items()}
spec = yaml.safe_load(Path("docs/MUTATION_BENCH.yaml").read_text(encoding="utf-8"))
missing = []
for rel in spec["bindings"]["cpp"]["hot_path"]:
    n = sum(c for path, c in counts.items() if path.endswith("/" + rel))
    print(f"  {n:4d} {rel}")
    if n == 0:
        missing.append(rel)
if missing:
    print("hot-path files with no mutant in the dry run: " + ", ".join(missing))
    sys.exit(1)
PY
