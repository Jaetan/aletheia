#!/usr/bin/env bash
# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
#
# Probes cpp/tests/fresh_process_tests.cpp and cpp/tests/test_rts_heap_cap.cpp.
# Claim: a process a fresh-process suite starts dies with the process that
# started it. The mutation runner ends a run by killing the test binary's pid
# alone and then waits for its pipes to close, so a child left running would
# hold them and stall the sweep. Each case points ALETHEIA_LIB at a FIFO, so
# the child that loads the kernel blocks opening it; the probe's own open of
# the FIFO returns once the child holds it, which says the child is running
# without a clock. The probe then kills the parent, reaps it, and reads the
# holder's state: gone, a zombie, or SIGKILL pending all mean the kernel is
# ending it with its parent. Two parents: the driver, whose child is the
# runtime-down suite, and the heap-cap suite, whose child is the workload.
# Non-zero exit: a child outlived its parent with no kill pending (the probe
# then kills it). Exits 2 when the normal build tree is not built.
set -u
cd "$(dirname "$0")/.." || exit 2
py=python/.venv/bin/python
[ -x "$py" ] || { echo "no $py"; exit 2; }
for bin in cpp/build/fresh_process_tests cpp/build/fresh-process/rts_heap_cap_tests; do
    [ -x "$bin" ] || { echo "$bin is not built: build cpp/build first"; exit 2; }
done
mkdir -p tools/ci-output || exit 2
exec "$py" - << 'PY'
import os
import signal
import subprocess
import sys
import tempfile
from pathlib import Path

ROOT = Path.cwd()
KILL_BIT = 1 << (signal.SIGKILL - 1)


def holders(fifo):
    """Every process but this one with ``fifo`` open."""
    found = []
    for proc in Path("/proc").iterdir():
        if not proc.name.isdigit() or int(proc.name) == os.getpid():
            continue
        try:
            fds = list((proc / "fd").iterdir())
        except OSError:
            continue
        for fd in fds:
            try:
                if os.readlink(fd) == str(fifo):
                    found.append(int(proc.name))
                    break
            except OSError:
                continue
    return found


def ending(pid):
    """True when ``pid`` is gone, a zombie, or has SIGKILL pending."""
    try:
        status = Path(f"/proc/{pid}/status").read_text(encoding="utf-8")
    except FileNotFoundError:
        return True
    fields = dict(line.split(":\t", 1) for line in status.splitlines() if ":\t" in line)
    if fields.get("State", "").startswith(("Z", "X")):
        return True
    pending = int(fields["SigPnd"], 16) | int(fields["ShdPnd"], 16)
    return bool(pending & KILL_BIT)


def case(label, argv):
    with tempfile.TemporaryDirectory(dir="tools/ci-output", prefix=".orphan-") as scratch:
        fifo = Path(scratch).resolve() / "libaletheia-ffi.so"
        os.mkfifo(fifo)
        env = {**os.environ, "ALETHEIA_LIB": str(fifo), "ALETHEIA_REPO_ROOT": str(ROOT)}
        parent = subprocess.Popen(argv, env=env, stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL)
        writer = os.open(fifo, os.O_WRONLY)
        held = holders(fifo)
        parent.kill()
        parent.wait()
        orphans = [pid for pid in held if not ending(pid)]
        for pid in orphans:
            os.kill(pid, signal.SIGKILL)
        os.close(writer)
    if not held:
        print(f"{label}: no child held the library open, so nothing was shown")
        return False
    if orphans:
        print(f"{label}: child {orphans} outlived its parent with no kill pending")
        return False
    print(f"{label}: child {held} ends with its parent")
    return True


results = [
    case(
        "driver",
        ["cpp/build/fresh_process_tests", "the renderer refuses while the runtime is down"],
    ),
    case(
        "heap-cap suite",
        ["cpp/build/fresh-process/rts_heap_cap_tests", "default cap boots and parses a workload"],
    ),
]
sys.exit(0 if all(results) else 1)
PY
