#!/usr/bin/env bash
# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
#
# Probes cpp/src/detail/loader_utils.hpp.
# Claim: the mutation lane sees the then-dispatcher. Its branches are
# string_view comparisons, which Mull's default mutators never touch, so the
# lane reported a clean score over a function it had never mutated; with the
# call mutators configured in cpp/mull.yml, a dry run over the mutation tree
# lists at least one mutant in this header, and every one of them is in the
# dispatcher or the predicates beside it rather than nowhere. The tree is read
# through a dry run of the lane's own command, in the lane's environment and
# directory, its report in scratch. Non-zero exit: the dry run lists no
# mutant in the header, or writes no report. Exits 0 with a note when Mull or
# the mutation tree is not available, since the claim is untestable then.
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

from tools.mutation_cpp_legs import CppLeg
from tools.mutation_cpp_dry_run import MULL_RUNNER, dry_run_report, lane_binary

if shutil.which(MULL_RUNNER) is None:
    print("Mull not installed, claim untestable")
    sys.exit(0)
if not os.access(lane_binary(), os.X_OK):
    print("no mutation tree built, claim untestable")
    sys.exit(0)
with tempfile.TemporaryDirectory(prefix="dry-run-") as scratch:
    report = dry_run_report(CppLeg(), Path(scratch))
    if isinstance(report, str):
        print(report)
        sys.exit(1)
    files = json.loads(report.read_text(encoding="utf-8"))["files"]

header = "cpp/src/detail/loader_utils.hpp"
mutants = [m for path, entry in files.items() if path.endswith(header) for m in entry.get("mutants", [])]
if not mutants:
    print(f"the dry run lists no mutant in {header}")
    sys.exit(1)
lines = sorted({m["location"]["start"]["line"] for m in mutants})
print(f"  {len(mutants)} mutants in {header} at lines {lines}")
PY
