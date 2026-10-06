# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
"""A process id no process holds, for the tests of code that reads one as gone."""

from __future__ import annotations

from pathlib import Path
from typing import NewType

# A process id, as the kernel numbers processes.
ProcessId = NewType("ProcessId", int)


def pid_no_process_holds() -> ProcessId:
    """Return the kernel's ``pid_max``, which it never hands out: ids run to one below it.

    A child spawned and reaped for its id would serve only until the kernel
    gave the id to another process.
    """
    return ProcessId(int(Path("/proc/sys/kernel/pid_max").read_text(encoding="ascii")))
