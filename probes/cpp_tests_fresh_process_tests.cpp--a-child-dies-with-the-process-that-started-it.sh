#!/usr/bin/env bash
# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
#
# Probes cpp/tests/fresh_process_tests.cpp and cpp/tests/test_rts_heap_cap.cpp.
# Claim: a process a fresh-process suite starts dies with the process that
# started it. The mutation runner ends a run by killing the test binary's pid
# alone and then waits for its pipes to close, so a child left running would
# hold them and stall the sweep. Each case puts a FIFO where the child loads
# the kernel from, so the child blocks opening it: the runtime-start suite
# opens the root's build/libaletheia-ffi.so, the root a scratch directory, and
# the heap-cap workload opens ALETHEIA_LIB. A process of the probe's own opens
# the FIFO for writing and says so once the child holds it, which says the
# child is running without a clock; the parent ending first says no child
# loaded the kernel. The probe then kills the parent, reaps it, and reads the
# holder's state: gone, a zombie, or SIGKILL pending all mean the kernel is
# ending it with its parent. Two parents: the driver, whose child is the
# runtime-start suite, and the heap-cap suite, whose child is the workload.
# Non-zero exit: a child outlived its parent with no kill pending (the probe
# then kills it). Exits 2 when the normal build tree is not built, or when no
# child of a parent opened the FIFO.
set -u
cd "$(dirname "$0")/.." || exit 2
py=python/.venv/bin/python
[ -x "$py" ] || { echo "no $py"; exit 2; }
for bin in cpp/build/fresh_process_tests cpp/build/rts_heap_cap_tests; do
    [ -x "$bin" ] || { echo "$bin is not built: build cpp/build first"; exit 2; }
done
exec "$py" - << 'PY'
import contextlib
import os
import select
import signal
import subprocess
import sys
import tempfile
from pathlib import Path

ROOT = Path.cwd()
KILL_BIT = 1 << (signal.SIGKILL - 1)


def holders(fifo, own):
    """Every process but this one and ``own`` with ``fifo`` open."""
    found = []
    for proc in Path("/proc").iterdir():
        if not proc.name.isdigit() or int(proc.name) in {os.getpid(), own}:
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
    """True when ``pid`` is gone, a zombie, or has SIGKILL pending.

    A process gone before the open raises FileNotFoundError; one gone between the open and the read
    raises ProcessLookupError. Either is gone.
    """
    try:
        status = Path(f"/proc/{pid}/status").read_text(encoding="utf-8")
    except (FileNotFoundError, ProcessLookupError):
        return True
    fields = dict(line.split(":\t", 1) for line in status.splitlines() if ":\t" in line)
    if fields.get("State", "").startswith(("Z", "X")):
        return True
    pending = int(fields["SigPnd"], 16) | int(fields["ShdPnd"], 16)
    return bool(pending & KILL_BIT)


def case(label, argv, root):
    """True when the child ends with its parent, False when it outlives it, None when no child loaded the kernel.

    ``root`` is the repository root the child reads: the scratch directory, whose
    build/libaletheia-ffi.so is the FIFO, or the tree.
    """
    with tempfile.TemporaryDirectory(prefix="orphan-") as scratch:
        top = Path(scratch).resolve()
        fifo = top / "build" / "libaletheia-ffi.so"
        fifo.parent.mkdir()
        os.mkfifo(fifo)
        env = {**os.environ, "ALETHEIA_LIB": str(fifo), "ALETHEIA_REPO_ROOT": str(root or top)}
        parent = subprocess.Popen(argv, env=env, stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL)
        # A writer's open blocks until a reader holds the FIFO, so it runs in a
        # process that holds the FIFO until its input closes, raced against the
        # parent's end.
        writer = subprocess.Popen(
            ["sh", "-c", 'exec 3>"$1" && echo held && exec cat >/dev/null', "sh", str(fifo)],
            stdin=subprocess.PIPE,
            stdout=subprocess.PIPE,
        )
        parent_end = os.pidfd_open(parent.pid)
        ready, _, _ = select.select([writer.stdout, parent_end], [], [])
        os.close(parent_end)
        if writer.stdout not in ready:
            writer.kill()
            writer.wait()
            parent.wait()
            print(f"{label}: no child loaded the kernel, so nothing was shown")
            return None
        held = holders(fifo, writer.pid)
        parent.kill()
        parent.wait()
        orphans = [pid for pid in held if not ending(pid)]
        for pid in orphans:
            with contextlib.suppress(ProcessLookupError):  # it may end between the check and the kill
                os.kill(pid, signal.SIGKILL)
        writer.stdin.close()
        writer.wait()
    if not held:
        print(f"{label}: no child held the library open, so nothing was shown")
        return None
    if orphans:
        print(f"{label}: child {orphans} outlived its parent with no kill pending")
        return False
    print(f"{label}: child {held} ends with its parent")
    return True


results = [
    case(
        "driver",
        [
            "cpp/build/fresh_process_tests",
            # Catch2 reads an unescaped comma as the end of one test spec.
            "the runtime starts before any client\\, and what read a number first keeps nothing",
        ],
        None,
    ),
    case(
        "heap-cap suite",
        ["cpp/build/rts_heap_cap_tests", "default cap boots and parses a workload"],
        ROOT,
    ),
]
if False in results:
    sys.exit(1)
sys.exit(2 if None in results else 0)
PY
