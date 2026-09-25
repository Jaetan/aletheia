#!/usr/bin/env bash
# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
#
# Probes tools/_common.py.
# Claim: the repo-wide Agda lock is not inherited by a process a tool starts,
# so it frees when the tool dies even while that process runs on. A lock
# descriptor a child inherited would keep the lock held under a dead recorded
# pid. The probe takes the lock through agda_tree_lock at a scratch lock path,
# starts a long-lived child that keeps every descriptor the lock left
# inheritable (close_fds=False, so the claim rests on the descriptor rather
# than on the spawn), SIGKILLs the tool and reads the lock while the child
# still runs. Every file it writes is under its scratch directory.
# Non-zero exit: 1 when the lock stays held after the tool died; 2 when the
# tool never took the lock.
set -u
cd "$(dirname "$0")/.." || exit 2
py=python/.venv/bin/python
[ -x "$py" ] || exit 2
scratch=$(mktemp -d) || exit 2
trap 'rm -rf "$scratch"' EXIT
"$py" - "$scratch" <<'PY'
import fcntl
import os
import signal
import subprocess
import sys
import textwrap
import time
from pathlib import Path

scratch = Path(sys.argv[1])
lock = scratch / ".agda-tree.lock"
child_pid = scratch / "child.pid"
tool = subprocess.Popen(
    [sys.executable, "-c", textwrap.dedent(f"""
        import subprocess
        from pathlib import Path
        from tools import _common
        _common._agda_lock_path = lambda: Path({str(lock)!r})
        with _common.agda_tree_lock():
            child = subprocess.Popen(["sleep", "60"], close_fds=False)
            Path({str(child_pid)!r}).write_text(str(child.pid))
            child.wait()
    """)],
)
deadline = time.monotonic() + 30
while not (child_pid.exists() and child_pid.read_text()):
    if time.monotonic() > deadline or tool.poll() is not None:
        print("the tool never took the lock")
        raise SystemExit(2)
    time.sleep(0.05)
child = int(child_pid.read_text())
os.kill(tool.pid, signal.SIGKILL)
_ = tool.wait()
fd = os.open(lock, os.O_RDWR)
try:
    fcntl.flock(fd, fcntl.LOCK_EX | fcntl.LOCK_NB)
    held = False
except BlockingIOError:
    held = True
finally:
    os.close(fd)
    os.kill(child, signal.SIGKILL)
if held:
    print(f"the lock is still held after the tool died, while its child pid {child} ran")
    raise SystemExit(1)
print("PASS: the lock freed when the tool died, with its child still running")
PY
