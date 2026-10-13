# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
"""The commands of a sweep's steps, answered in-process in place of ``run_guarded``.

A test gives every step command it registers a stand-in: what the command does
to the files it reaches, the output it writes and the status it ends with.
:class:`StepRuns`, installed as ``tools._scheduler.run_guarded`` by
:func:`install`, records each command the scheduler asks for with the
directory and the stop descriptor it hands over, fails the test on a command
that has no stand-in, and answers the rest without starting a process.  What
a command and its guard do between processes, the status a signal leaves and
the order of a merged stream, is held by ``test_run_guarded``.
"""

from __future__ import annotations

import subprocess
from dataclasses import dataclass
from typing import TYPE_CHECKING, NewType

from _processes import CommandWord

from tools import _scheduler

from aletheia.common_types import ExitStatus, Prose

if TYPE_CHECKING:
    from collections.abc import Callable, Mapping
    from pathlib import Path

    import pytest

# An open file descriptor of this process.
Descriptor = NewType("Descriptor", int)

# The shell and the flag the scheduler runs a step's command text under.
_SHELL = (CommandWord("/bin/sh"), CommandWord("-c"))

# The output of a command that writes nothing.
NO_OUTPUT = Prose("")


@dataclass(frozen=True)
class StepCall:
    """One command the scheduler asked to run, with the directory and stop descriptor it gave."""

    command: CommandWord
    cwd: Path | None
    stop_fd: Descriptor | None


@dataclass(frozen=True)
class Answer:
    """How a stand-in command ends: its status and its merged output."""

    status: ExitStatus
    output: Prose = NO_OUTPUT


# What a step command does, in-process: any effect on the files, then its answer.
type StandIn = Callable[[StepCall], Answer]


def ends(status: ExitStatus, output: Prose = NO_OUTPUT) -> StandIn:
    """Return a stand-in that writes ``output`` and ends with ``status``, touching nothing."""

    def answer(_call: StepCall) -> Answer:
        return Answer(status, output)

    return answer


def passes(_call: StepCall) -> Answer:
    """Stand in for a command that succeeds, writing nothing and touching nothing."""
    return Answer(ExitStatus(0))


class StepRuns:
    """A stand-in for ``run_guarded`` that answers each step command from a table."""

    def __init__(self, stand_ins: Mapping[CommandWord, StandIn]) -> None:
        """Answer the commands ``stand_ins`` names, and fail on any other."""
        self._stand_ins = stand_ins
        self.calls: list[StepCall] = []

    def __call__(
        self, cmd: list[CommandWord], *, cwd: Path | None, stop_fd: Descriptor | None
    ) -> subprocess.CompletedProcess[Prose]:
        """Record ``cmd`` and answer it as its stand-in does.

        The scheduler hands a step's command text to ``/bin/sh -c``; an argv of
        any other shape, or a command with no stand-in, fails the test.
        """
        shell, flag, command = cmd
        assert (shell, flag) == _SHELL, cmd
        call = StepCall(command, cwd, stop_fd)
        self.calls.append(call)
        answer = self._stand_ins[command](call)
        return subprocess.CompletedProcess(cmd, answer.status, answer.output, NO_OUTPUT)

    @property
    def commands(self) -> list[CommandWord]:
        """The command texts asked for, in the order the scheduler asked."""
        return [call.command for call in self.calls]


def install(monkeypatch: pytest.MonkeyPatch, stand_ins: Mapping[CommandWord, StandIn]) -> StepRuns:
    """Answer every step the scheduler runs from ``stand_ins`` for the rest of the test."""
    runs = StepRuns(stand_ins)
    monkeypatch.setattr(_scheduler, "run_guarded", runs)
    return runs
