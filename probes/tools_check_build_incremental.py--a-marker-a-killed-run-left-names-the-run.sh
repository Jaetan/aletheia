#!/usr/bin/env bash
# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
#
# Probes tools/check_build_incremental.py.
# Claim: a marker a killed run left in a probed source refuses the next run
# before it builds or captures anything, naming the run that wrote it, whether
# that run still lives, the file, and the edit that restores it. The probe
# plants the marker of a run that has already exited, runs the gate, and reads
# the refusal; the library and Shake's database keep their timestamps, which
# is how a build that did not happen is told from one that did.
# Non-zero exit: 1 when the gate passes, builds, or refuses without naming the
# run, the file and the repair; 2 when the source is not clean to begin with,
# there is no library to keep, or another Agda tool holds the lock.
set -u
cd "$(dirname "$0")/.." || exit 2
py=python/.venv/bin/python
[ -x "$py" ] || exit 2
src=src/Aletheia/Protocol/ResponseFormat.agda
git diff --quiet -- "$src" || { echo "$src carries uncommitted edits; the probe will not write over them"; exit 2; }
[ -f build/libaletheia-ffi.so ] || { echo "no build/libaletheia-ffi.so; build first"; exit 2; }
trap 'git checkout --quiet -- "$src"' EXIT
"$py" - "$src" <<'PY'
import subprocess
import sys
from pathlib import Path

sys.path.insert(0, ".")
from tools.check_build_incremental import MARKER_PREFIX  # noqa: E402

src = Path(sys.argv[1])
original = src.read_text(encoding="utf-8")
anchor = '"uncached_atom"'
if anchor not in original:
    print(f"the gate's anchor {anchor} is gone from {src}")
    raise SystemExit(2)
with subprocess.Popen([sys.executable, "-c", "pass"]) as child:
    child.wait()
marker = f"{MARKER_PREFIX}RF_pid{child.pid}_20260918T000000Z"
so = Path("build/libaletheia-ffi.so")
db = Path("build/.shake.database")


def stamps():
    return so.stat().st_mtime_ns, db.stat().st_mtime_ns if db.exists() else None


before = stamps()
src.write_text(original.replace(anchor, f'"uncached_atom_{marker}"'), encoding="utf-8")
try:
    run = subprocess.run(
        [sys.executable, "-m", "tools.check_build_incremental"],
        capture_output=True, text=True, check=False,
    )
finally:
    src.write_text(original, encoding="utf-8")
out = run.stdout + run.stderr
if "holds .agda-tree.lock" in out:
    print("another Agda tool holds the lock, so the gate could not be driven")
    raise SystemExit(2)

bad = []
if run.returncode == 0:
    bad.append("the gate passed over a marked source")
run_named = f"carries the marker of an interrupted gate run (pid {child.pid}, started 20260918T000000Z, gone)"
if run_named not in out:
    bad.append("the refusal does not name the run, its start and that it is gone")
if str(src) not in out:
    bad.append(f"the refusal does not name {src}")
if f'restore it by replacing "uncached_atom_{marker}" with {anchor}' not in out:
    bad.append("the refusal does not print the edit that restores the file")
if stamps() != before:
    bad.append("the gate built over the marked source: the library or Shake's database was rewritten")
if bad:
    print("a marker a killed run left does not refuse the gate the way it should:")
    for line in bad:
        print(f"  {line}")
    print(out[-800:])
    raise SystemExit(1)
print(f"PASS: the gate refused on the marker of run {child.pid}, named it and its repair, and built nothing")
PY
