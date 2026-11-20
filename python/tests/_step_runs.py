# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
"""The commands of a sweep's steps, answered in-process in place of ``run_watched``.

A test gives every step command it registers a stand-in: what the command does
to the files it reaches, the output it writes, the status it ends with, whether
it stalled and its longest quiet stretch.  :class:`StepRuns`, installed as
``tools._scheduler.run_watched`` by :func:`install`, records each command the
scheduler asks for with the directory and the stop descriptor it hands over,
fails the test on a command that has no stand-in, and answers the rest without
starting a process.  What only a started process shows is held by the tests
that start one: ``test_run_guarded`` holds the guard's stop, a signal's status
and the order of a merged stream for ``run_guarded``, and the stop and status
of a step ``run_watched`` finds stalled; ``test_scheduler``'s real step holds
the order of ``run_watched``'s merged stream.
"""

from __future__ import annotations

from dataclasses import dataclass
from typing import TYPE_CHECKING

from _processes import CommandWord

from tools import _scheduler
from tools._common import Descriptor, ProcessStatus
from tools._watchdog import Line, Pumped, ReportCount, Seconds, WatchedRun

from aletheia.common_types import ExitStatus, Prose

if TYPE_CHECKING:
    from collections.abc import Callable, Mapping
    from pathlib import Path

    import pytest

    from tools._watchdog import StepWatch


# The shell and the flag the scheduler runs a step's command text under.
_SHELL = (CommandWord("/bin/sh"), CommandWord("-c"))

# The output of a command that writes nothing.
NO_OUTPUT = Prose("")

# The longest quiet stretch a stand-in answers when its test names none.
_NO_QUIET = Seconds(0.0)


@dataclass(frozen=True)
class StepCall:
    """One command the scheduler asked to run, with the directory and stop descriptor it gave."""

    command: CommandWord
    cwd: Path | None
    stop_fd: Descriptor | None


@dataclass(frozen=True)
class Answer:
    """How a stand-in command ends: its status, its merged output, whether it stalled, its quiet.

    ``longest_quiet`` is the longest stretch the watchdog would have measured
    with no report.
    """

    status: ExitStatus
    output: Prose = NO_OUTPUT
    stalled: bool = False
    longest_quiet: Seconds = _NO_QUIET


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
    """A stand-in for ``run_watched`` that answers each step command from a table."""

    def __init__(self, stand_ins: Mapping[CommandWord, StandIn]) -> None:
        """Answer the commands ``stand_ins`` names, and fail on any other."""
        self._stand_ins = stand_ins
        self.calls: list[StepCall] = []

    def __call__(
        self,
        cmd: list[CommandWord],
        *,
        cwd: Path | None,
        stop_fd: Descriptor | None,
        watch: StepWatch,
    ) -> WatchedRun:
        """Record ``cmd`` and answer it as its stand-in does, through the watch it is handed.

        The scheduler hands a step's command text to ``/bin/sh -c``; an argv of
        any other shape, or a command with no stand-in, fails the test.  The
        answer's output goes into the step's file, each of its lines the step's
        progress pattern matches reaching the watch as a report.
        """
        shell, flag, command = cmd
        assert (shell, flag) == _SHELL, cmd
        call = StepCall(command, cwd, stop_fd)
        self.calls.append(call)
        answer = self._stand_ins[command](call)
        _ = watch.written.write(answer.output.encode())
        reports = [
            Line(line) for line in answer.output.splitlines() if watch.progress.reports(Line(line))
        ]
        for report in reports:
            watch.on_report(report)
        lines = answer.output.splitlines()
        pumped = Pumped(
            stalled=answer.stalled,
            reports=ReportCount(len(reports)),
            longest_quiet=answer.longest_quiet,
            last_report=reports[-1] if reports else Line(""),
            last_line=Line(lines[-1]) if lines else Line(""),
            ran_for=Seconds(0.0),
        )
        return WatchedRun(ProcessStatus(answer.status), pumped)

    @property
    def commands(self) -> list[CommandWord]:
        """The command texts asked for, in the order the scheduler asked."""
        return [call.command for call in self.calls]


def install(monkeypatch: pytest.MonkeyPatch, stand_ins: Mapping[CommandWord, StandIn]) -> StepRuns:
    """Answer every step the scheduler runs from ``stand_ins`` for the rest of the test."""
    runs = StepRuns(stand_ins)
    monkeypatch.setattr(_scheduler, "run_watched", runs)
    return runs
