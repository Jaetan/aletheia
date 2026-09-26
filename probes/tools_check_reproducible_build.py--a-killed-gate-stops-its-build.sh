#!/usr/bin/env bash
# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
#
# Probes tools/check_reproducible_build.py.
# Claim: when the gate dies mid-build, SIGKILL included, the build it started
# stops with it, and the lock that build held is free within 5 seconds. A
# build that outlives the gate keeps Shake's lock and races the next build.
# The probe runs the gate's clean-build step with a stand-in `cabal` first on
# PATH: the stand-in takes a lock and leaves a sleeping grandchild holding it,
# the shape of `cabal` running `shake`. The probe SIGKILLs the process running
# the step and reads the grandchild and the lock. Every file it writes is
# under its scratch directory.
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

gate = subprocess.Popen(
    [
        sys.executable,
        "-c",
        "import sys; from pathlib import Path; "
        + "from tools.check_reproducible_build import _run_clean_build; "
        + "_run_clean_build(1, Path(sys.argv[1]), Path(sys.argv[1]) / 'lib1.so')",
        str(scratch),
    ],
    stdout=subprocess.DEVNULL,
    stderr=subprocess.DEVNULL,
)
deadline = time.monotonic() + 30
while not (pid_file.exists() and pid_file.read_text().strip()):
    if time.monotonic() > deadline or gate.poll() is not None:
        print("the stand-in build never started")
        raise SystemExit(2)
    time.sleep(0.05)
grandchild = int(pid_file.read_text())

os.kill(gate.pid, signal.SIGKILL)
_ = gate.wait()
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
        print(f"the build outlived the killed gate by more than {bound:g}s (pid {grandchild})")
        raise SystemExit(1)
    time.sleep(0.05)
print(f"PASS: the build stopped {time.monotonic() - killed_at:.2f}s after the gate was killed")
PY
