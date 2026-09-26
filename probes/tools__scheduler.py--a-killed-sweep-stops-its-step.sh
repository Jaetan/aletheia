#!/usr/bin/env bash
# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
#
# Probes tools/_scheduler.py.
# Claim: when the sweep dies, SIGKILL included, a step it is running stops
# with it, and the lock that step held is free within 5 seconds. A build left
# running after the sweep is gone keeps Shake's lock and races the next build.
# The probe runs two lanes in parallel, one of them a step running a stand-in
# `cabal` first on PATH: the stand-in takes a lock and leaves a sleeping
# grandchild holding it, the shape of `cabal` running `shake`. The probe
# SIGKILLs the sweep and reads the grandchild and the lock. Every file it
# writes is under its scratch directory.
# Non-zero exit: 1 when the grandchild survives or the lock stays held past
# the bound; 2 when the stand-in never started.
set -u
cd "$(dirname "$0")/.." || exit 2
py=python/.venv/bin/python
[ -x "$py" ] || exit 2
flock_bin=$(command -v flock) || exit 2
scratch=$(mktemp -d) || exit 2
trap 'rm -rf "$scratch"' EXIT
mkdir "$scratch/bin"
cat > "$scratch/bin/cabal" <<STANDIN
#!/usr/bin/env bash
exec "$flock_bin" "$scratch/build.lock" sh -c 'echo \$\$ > "$scratch/grandchild.pid"; exec sleep 60'
STANDIN
chmod +x "$scratch/bin/cabal"
PATH=$scratch/bin:$PATH "$py" - "$scratch" <<'PY'
import contextlib
import fcntl
import os
import signal
import subprocess
import sys
import time
from pathlib import Path

scratch = Path(sys.argv[1])
pid_file = scratch / "grandchild.pid"
bound = 5.0

sweep = subprocess.Popen(
    [
        sys.executable,
        "-c",
        "from tools._scheduler import Step, run_lanes; "
        + "run_lanes([[Step('build', 'cabal run shake -- build')], [Step('other', 'true')]], "
        + "max_workers=2, heavy_limit=1)",
    ],
    stdout=subprocess.DEVNULL,
    stderr=subprocess.DEVNULL,
)
deadline = time.monotonic() + 30
while not (pid_file.exists() and pid_file.read_text().strip()):
    if time.monotonic() > deadline or sweep.poll() is not None:
        print("the stand-in build never started")
        raise SystemExit(2)
    time.sleep(0.05)
grandchild = int(pid_file.read_text())

os.kill(sweep.pid, signal.SIGKILL)
_ = sweep.wait()
killed_at = time.monotonic()


def alive(pid: int) -> bool:
    try:
        os.kill(pid, 0)
    except ProcessLookupError:
        return False
    return True


def lock_free() -> bool:
    fd = os.open(scratch / "build.lock", os.O_RDWR)
    try:
        fcntl.flock(fd, fcntl.LOCK_EX | fcntl.LOCK_NB)
    except BlockingIOError:
        return False
    finally:
        os.close(fd)
    return True


while alive(grandchild) or not lock_free():
    if time.monotonic() - killed_at > bound:
        with contextlib.suppress(ProcessLookupError):
            os.kill(grandchild, signal.SIGKILL)
        print(f"the build outlived the killed sweep by more than {bound:g}s (pid {grandchild})")
        raise SystemExit(1)
    time.sleep(0.05)
print(f"PASS: the build stopped {time.monotonic() - killed_at:.2f}s after the sweep was killed")
PY
