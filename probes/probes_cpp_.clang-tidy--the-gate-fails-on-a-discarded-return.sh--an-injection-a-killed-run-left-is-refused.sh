#!/usr/bin/env bash
# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
#
# Probes probes/cpp_.clang-tidy--the-gate-fails-on-a-discarded-return.sh.
# Claim: when a source still carries the injection of an earlier run, the
# probe refuses before it runs the gate or captures the source, naming the run
# that injected it and whether that run still lives. A run killed between an
# injection and its restore once left `Dlc::create(8);` in a tracked source,
# and the next run captured that text as its own original. The injection of a
# run that has exited is planted into the library source, the probe is run,
# and its refusal read.
# Non-zero exit: 1 when the probe runs on, passes, or refuses without naming
# the run; 2 when the source is not clean to begin with, or the toolchain the
# probed probe needs is absent, in which case it too exits 2.
set -u
cd "$(dirname "$0")/.." || exit 2
probe=probes/cpp_.clang-tidy--the-gate-fails-on-a-discarded-return.sh
command -v run-clang-tidy-23 > /dev/null || { echo "run-clang-tidy-23 not installed"; exit 0; }
[ -f cpp/build/compile_commands.json ] || { echo "no compile database; configure cpp/build"; exit 2; }
src=cpp/src/types.cpp
git diff --quiet -- "$src" || { echo "$src carries uncommitted edits; the probe will not write over them"; exit 2; }
trap 'git checkout --quiet -- "$src"' EXIT
python/.venv/bin/python - "$probe" "$src" <<'PY'
import subprocess
import sys
from pathlib import Path

probe, src = sys.argv[1], Path(sys.argv[2])
original = src.read_text(encoding="utf-8")
point = "namespace aletheia {"
if point not in original:
    print(f"the injection point is gone from {src}")
    raise SystemExit(2)
with subprocess.Popen([sys.executable, "-c", "pass"]) as child:
    child.wait()
left = (f"\n\nvoid probe_discard() {{ Dlc::create(8); }}"
        f"  // injected by the clang-tidy probe, run pid {child.pid}\n")
src.write_text(original.replace(point, point + left, 1), encoding="utf-8")
try:
    run = subprocess.run(["bash", probe], capture_output=True, text=True, check=False)
finally:
    src.write_text(original, encoding="utf-8")
out = run.stdout + run.stderr
bad = []
if run.returncode != 2:
    bad.append(f"the probe exited {run.returncode}, not 2, over a source carrying an earlier injection")
named = f"{src} still carries the injection of an earlier run of this probe (pid {child.pid}, gone)"
if named not in out:
    bad.append("the refusal does not name the file, the run and that it is gone")
if bad:
    print("an injection a killed run left is not refused the way it should be:")
    for line in bad:
        print(f"  {line}")
    print(out[-800:])
    raise SystemExit(1)
print(f"PASS: the probe refused on the injection of run {child.pid} and named it")
PY
