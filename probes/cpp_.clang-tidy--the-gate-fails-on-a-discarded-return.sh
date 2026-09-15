# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
#
# Probes the clang-tidy gate over cpp/src.
# Claim: the gate reports a defect it is configured to catch, and a run that
# enabled no checks is not mistaken for a clean one. A discarded nodiscard
# return is injected into a library source and removed again by the same
# step. Non-zero exit: the gate accepts the injected defect, the tree is not
# clean to begin with, or a run from the repository root, where no
# configuration is found, passes the same output test as a real run.
set -u
cd "$(dirname "$0")/.." || exit 2
command -v run-clang-tidy-22 > /dev/null || { echo "run-clang-tidy-22 not installed"; exit 0; }
[ -f cpp/build/compile_commands.json ] || { echo "no compile database; configure cpp/build"; exit 2; }
python/.venv/bin/python - <<'PY'
import subprocess
import sys
from pathlib import Path

source = Path("cpp/src/types.cpp")
marker = "namespace aletheia {"
original = source.read_text(encoding="utf-8")
if marker not in original:
    print("the injection point is gone from the library source")
    raise SystemExit(2)


def gate(cwd: str) -> subprocess.CompletedProcess[str]:
    return subprocess.run(
        ["run-clang-tidy-22", "-quiet", "-p", "build" if cwd == "cpp" else "cpp/build", "cpp/src/"],
        cwd=cwd,
        capture_output=True,
        text=True,
        check=False,
    )


clean = gate("cpp")
if "error:" in clean.stdout or "warning:" in clean.stdout:
    print(f"the tree is not clean before the injection:\n{clean.stdout[:400]}")
    raise SystemExit(1)

try:
    source.write_text(
        original.replace(marker, marker + "\n\nvoid probe_discard() { Dlc::create(8); }\n", 1),
        encoding="utf-8",
    )
    injected = gate("cpp")
    from_root = gate(".")
finally:
    source.write_text(original, encoding="utf-8")

if "clang-diagnostic-unused-result" not in injected.stdout:
    print(f"the gate did not report the discarded return:\n{injected.stdout[:400]}")
    raise SystemExit(1)
# The root-relative run enables no checks.  It must not look like the clean
# run above, or a reader grepping for a finding reads it as a pass.
if "No checks enabled" not in from_root.stdout + from_root.stderr:
    print("a run with no configuration in scope no longer says so")
    raise SystemExit(1)
if "error:" in from_root.stdout:
    print("a run with no configuration in scope unexpectedly reported findings")
    raise SystemExit(1)
sys.exit(0)
PY
