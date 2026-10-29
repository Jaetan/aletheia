# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
"""What a git hook the tests load wrote and answered, shared by the hooks' tests."""

from __future__ import annotations

import contextlib
import io
import subprocess
from typing import TYPE_CHECKING, NamedTuple, NewType

from aletheia.common_types import ExitStatus, Prose

if TYPE_CHECKING:
    from collections.abc import Callable

# What a git process wrote, what a tool the hook runs wrote, and the work
# tree's root as git prints it.
GitOutput = NewType("GitOutput", str)
ToolOutput = NewType("ToolOutput", str)
TopLevel = NewType("TopLevel", str)
GitDone = subprocess.CompletedProcess[GitOutput]
ToolDone = subprocess.CompletedProcess[ToolOutput]


class HookRun(NamedTuple):
    """What a hook answered: its exit status and what it wrote to stderr."""

    returncode: ExitStatus
    stderr: Prose


def run_main(main: Callable[[], ExitStatus]) -> HookRun:
    """Run a loaded hook's ``main`` with its stderr captured."""
    captured = io.StringIO()
    with contextlib.redirect_stderr(captured):
        rc = main()
    return HookRun(rc, Prose(captured.getvalue()))
