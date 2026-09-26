# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
"""Run a command that stops when the process that started it dies, however it dies.

Usage: ``python tools/_guarded_run.py <watch-fds> <grace-seconds> <command>...``

The caller starts this script as the leader of a new process group and passes
it, comma-separated, the read ends of pipes whose write ends only the caller
holds and never writes.  A read end therefore reports end-of-file exactly when
the caller closes its write end or dies, SIGKILL included, since the kernel
closes a dead process's descriptors.  At end-of-file on any of them the script
sends SIGINT to its group,
the signal a terminal's Ctrl-C delivers to a foreground job: Shake answers it
by killing the process groups it made for its own children and exiting, and
``cabal`` exits once Shake has.  Once the command exits, or ``<grace-seconds>``
after the interrupt if it has not, the group gets SIGKILL, which ends whatever
ignored the interrupt and this script too.

The script exits with the command's status, or 128 plus the signal number
when a signal ended the command, and refuses with status 2 when it does not
lead its own process group.  It imports only the standard library, and
is run by path rather than as ``tools._guarded_run`` so it works from any
working directory.
"""

from __future__ import annotations

import contextlib
import os
import select
import signal
import subprocess
import sys
import threading


def _status(returncode: int) -> int:
    """Map a ``Popen`` return code to a shell exit status."""
    return 128 - returncode if returncode < 0 else returncode


def _stop_on_end_of_file(
    watch_fds: list[int], grace: float, child: subprocess.Popen[bytes], stopping: threading.Event
) -> None:
    """Block until one of ``watch_fds`` reads end-of-file, then stop the group."""
    while all(os.read(fd, 1) for fd in select.select(watch_fds, [], [])[0]):
        pass  # the caller never writes; anything read is discarded
    stopping.set()
    os.killpg(0, signal.SIGINT)
    with contextlib.suppress(subprocess.TimeoutExpired):
        _ = child.wait(timeout=grace)
    # Whatever is still in the group ignored the interrupt or outlived the command.
    os.killpg(0, signal.SIGKILL)


def main(argv: list[str]) -> int:
    """Run ``argv[2:]``, stopping its group when a descriptor ``argv[0]`` lists reads end-of-file.

    ``argv[1]`` is the grace period in seconds between the interrupt and SIGKILL.
    """
    if os.getpgrp() != os.getpid():
        # Stopping the group would signal the caller's own group, the caller included.
        _ = sys.stderr.write("_guarded_run.py: not the leader of its own process group; refusing\n")
        return 2
    watch_fds = [int(fd) for fd in argv[0].split(",")]
    grace = float(argv[1])
    with subprocess.Popen(argv[2:]) as child:
        # Set only once the child runs, so the command keeps the default disposition.
        _ = signal.signal(signal.SIGINT, signal.SIG_IGN)
        stopping = threading.Event()
        watcher = threading.Thread(
            target=_stop_on_end_of_file, args=(watch_fds, grace, child, stopping), daemon=True
        )
        watcher.start()
        status = _status(child.wait())
    if stopping.is_set():
        watcher.join()  # ends in the SIGKILL of this group, this script included
    return status


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
