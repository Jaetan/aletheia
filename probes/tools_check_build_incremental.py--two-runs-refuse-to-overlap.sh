#!/usr/bin/env bash
# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
#
# Probes tools/check_build_incremental.py.
# Claim: while another Agda tool holds the repo-wide lock, a run of the gate
# exits naming the holder, and it neither edits a source nor builds. Two runs
# that overlapped would each capture the other's edit as its own original and
# write it back as the restore. The probe holds the lock itself, runs the gate,
# and reads the refusal; the two probed sources and the library are compared
# before and after.
# Non-zero exit: 1 when the gate ran under a held lock, or refused without
# naming the holder, or touched a source or the library; 2 when the probe
# could not take the lock or there is no library to compare.
set -u
cd "$(dirname "$0")/.." || exit 2
py=python/.venv/bin/python
[ -x "$py" ] || exit 2
[ -f build/libaletheia-ffi.so ] || { echo "no build/libaletheia-ffi.so; build first"; exit 2; }
"$py" - <<'PY'
import fcntl
import os
import subprocess
import sys
from pathlib import Path

fd = os.open(".agda-tree.lock", os.O_CREAT | os.O_RDWR, 0o644)
try:
    fcntl.flock(fd, fcntl.LOCK_EX | fcntl.LOCK_NB)
except BlockingIOError:
    print("another Agda tool holds .agda-tree.lock; the probe cannot stage its contention")
    raise SystemExit(2)
os.ftruncate(fd, 0)
os.write(fd, f"{os.getpid()}\n".encode())

sources = [
    Path("src/Aletheia/Protocol/ResponseFormat.agda"),
    Path("src/Aletheia/DBC/Formatter.agda"),
]
so = Path("build/libaletheia-ffi.so")
before = [s.read_bytes() for s in sources] + [so.stat().st_mtime_ns]
run = subprocess.run(
    [sys.executable, "-m", "tools.check_build_incremental"],
    capture_output=True, text=True, check=False,
)
after = [s.read_bytes() for s in sources] + [so.stat().st_mtime_ns]

bad = []
if run.returncode == 0:
    bad.append("the gate ran to a pass while this probe held the lock")
holder = f"another Agda tool holds .agda-tree.lock (pid {os.getpid()}, alive)"
if holder not in run.stderr:
    bad.append("the refusal does not name this probe as the holder")
if before != after:
    bad.append("a source or the library changed under the refused run")
if bad:
    print("a second run of the gate does not refuse the way it should:")
    for line in bad:
        print(f"  {line}")
    print((run.stdout + run.stderr)[-800:])
    raise SystemExit(1)
print(f"PASS: the gate reported the lock held by pid {os.getpid()} and touched nothing")
PY
