#!/usr/bin/env bash
# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
#
# Probes tools/coverage_run.py.
# Claim: the C++ export is handed every executable ctest would run in the
# coverage tree and every shared library the tree built, so a source linked
# into one binary alone is counted: the object list is read from ctest's own
# listing, and the export's argv names each of them. The export itself is
# replaced by a recorder, so nothing runs and the tree is only read.
# Non-zero exit: an executable ctest lists, or a shared library of the tree,
# is missing from the export's argv. Exits 2 when cpp/build-coverage is not
# configured; the coverage lane (tools/run_ci.py --coverage) configures it.
set -u
cd "$(dirname "$0")/.." || exit 2
[ -f cpp/build-coverage/CMakeCache.txt ] || exit 2

python/.venv/bin/python - <<'PY' || exit 1
import json
import subprocess
import sys
import tempfile
from pathlib import Path

from tools import coverage_run

build = coverage_run.CPP_BUILD_DIR
listing = json.loads(
    subprocess.run(
        ["ctest", "--test-dir", str(build), "--show-only=json-v1"],
        check=True,
        capture_output=True,
        text=True,
    ).stdout
)
expected_objects = {t["command"][0] for t in listing["tests"]}
expected_libs = {str(p) for p in build.glob("*.so*") if p.is_file() and not p.is_symlink()}
if not expected_objects or not expected_libs:
    print("the tree lists no test executable or built no shared library")
    sys.exit(1)

recorded: list[list[str]] = []
canned = json.dumps({"data": [{"totals": {"lines": {"covered": 1, "count": 1},
                                          "branches": {"covered": 1, "count": 1}},
                               "files": []}]})


def fake(cmd: list[str], **_kw: object) -> subprocess.CompletedProcess[str]:
    recorded.append(cmd)
    if cmd[0].startswith("llvm-cov"):
        return subprocess.CompletedProcess(cmd, 0, stdout=canned, stderr="")
    return subprocess.run(cmd, capture_output=True, text=True, check=False)


coverage_run.run_capture = fake
with tempfile.TemporaryDirectory() as tmp:
    profdata = Path(tmp) / "x.profdata"
    profdata.write_bytes(b"")
    coverage_run._cpp_export(profdata, Path(tmp))  # noqa: SLF001

export = next(cmd for cmd in recorded if cmd[0].startswith("llvm-cov"))
named = set(export)
missing = sorted((expected_objects | expected_libs) - named)
if missing:
    print("absent from the export's argv:")
    for m in missing:
        print("  " + m)
    sys.exit(1)
print(f"{len(expected_objects)} executables and {len(expected_libs)} libraries named")
PY
exit 0
