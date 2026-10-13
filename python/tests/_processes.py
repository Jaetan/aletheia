# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
"""A process as the tests name one: its id, and the words of its command line."""

from __future__ import annotations

from pathlib import Path
from typing import NewType

# A process id, as the kernel numbers processes.
ProcessId = NewType("ProcessId", int)

# One word of a command line, as the shell splits it: the program, a flag or an argument.
CommandWord = NewType("CommandWord", str)


def pid_no_process_holds() -> ProcessId:
    """Return the kernel's ``pid_max``, which it never hands out: ids run to one below it.

    A child spawned and reaped for its id would serve only until the kernel
    gave the id to another process.
    """
    return ProcessId(int(Path("/proc/sys/kernel/pid_max").read_text(encoding="ascii")))
