# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
"""A step's output read as it comes, its progress reports picked out, and a deadline on them.

A step reports its progress itself, in its own output: a line its
:class:`Progress` pattern matches, carrying how much of its work is done, as
``done`` and ``total`` or as a ``percent``.  :func:`pump` copies the step's
output into its file as each chunk arrives and reads every line of it.  Each
report moves the step's deadline to ``allowance`` after it; the first deadline
is ``allowance`` after the step started.  The pump waits for output only until
the deadline, so nothing ticks: when output comes it is read at once, and when
the deadline passes with no report the pump answers that the step stalled,
naming its last report and its last line.

A :class:`Progress` with no allowance holds no deadline: the pump records the
longest stretch between reports, counted from the step's start to its first
report and from its last report to its end, from which an allowance is set.

A carriage return ends a line as a newline does, since a progress bar redrawn
in place writes one per redraw.

:func:`run_watched` runs a command as ``tools._common.run_guarded`` does, its
output read through :func:`pump`, and stops it through its guard on a stall.
"""

from __future__ import annotations

import os
import re
import select
import subprocess
import time
from dataclasses import dataclass
from typing import TYPE_CHECKING, NewType

from tools._common import CommandWord, Descriptor, GraceSeconds, ProcessStatus, under_the_guard

from aletheia.common_types import Prose

if TYPE_CHECKING:
    from collections.abc import Callable, Sequence
    from pathlib import Path
    from typing import BinaryIO

# A reading of the monotonic clock, or a stretch of it, in seconds; a line of a step's output, its
# ends stripped; a chunk of a step's output as it arrived; the regular expression a report
# matches; how many reports a step made; the share of its work a report says is done, 0 to 1.
Seconds = NewType("Seconds", float)
Line = NewType("Line", str)
Chunk = NewType("Chunk", bytes)
PatternText = NewType("PatternText", str)
ReportCount = NewType("ReportCount", int)
Share = NewType("Share", float)

_LINE_END = re.compile(rb"[\r\n]")


@dataclass(frozen=True)
class Progress:
    """How a step reports progress: which lines are reports, how long it may go without one.

    ``pattern`` matches a report and names its share of the work done, by the
    groups ``done`` and ``total`` or by ``percent``; ``allowance`` is the most
    the step may go without a report, ``None`` while it is being measured.
    """

    pattern: PatternText
    allowance: Seconds | None = None

    @property
    def expects_reports(self) -> bool:
        """Answer whether the step reports its progress at all, or prints no count."""
        return self.pattern != NEVER

    def reports(self, line: Line) -> bool:
        """Answer whether ``line`` is one of this step's progress reports."""
        return re.search(self.pattern, line) is not None

    def share(self, report: Line) -> Share | None:
        """Return how much of its work ``report`` says is done, or ``None`` if it says not.

        A pattern holding several tools' counts names each ``percent`` or
        ``done`` and ``total`` group with a suffix of its own, ``done_2`` beside
        ``total_2``: the matched one is read.
        """
        found = re.search(self.pattern, report)
        if found is None:
            return None
        for name, value in found.groupdict().items():
            if value is None:
                continue
            if name.startswith("percent"):
                return Share(min(1.0, int(value) / 100))
            if name.startswith("done"):
                total = found.groupdict().get("total" + name.removeprefix("done"))
                return Share(min(1.0, int(value) / int(total))) if total and int(total) else None
        return None


# The pattern no line matches, and the progress of a step that reports nothing: no deadline is held
# by a report of its, so the watchdog only measures it until its allowance is set.
NEVER = PatternText(r"(?!)")
NO_REPORTS_YET = Progress(NEVER)


@dataclass(frozen=True)
class Pumped:
    """What the pump read of a step: whether it stalled, and its reports.

    ``stalled`` is true when the deadline passed with no report; ``reports``
    counts them; ``longest_quiet`` is the longest stretch with none, its start
    and end included; ``last_report`` and ``last_line`` are the last of each,
    empty when there was none; ``ran_for`` is how long the step ran, on the
    clock its output was read by.
    """

    stalled: bool
    reports: ReportCount
    longest_quiet: Seconds
    last_report: Line
    last_line: Line
    ran_for: Seconds


@dataclass(frozen=True)
class Output:
    """A step's output as the pump reads it, and the clock it is timed by.

    ``read`` answers the next chunk, empty once the output has ended, and is
    called only once ``readable_within`` answered that output is ready within
    the stretch it was given (``None``: however long it takes).
    """

    read: Callable[[], Chunk]
    readable_within: Callable[[Seconds | None], bool]
    now: Callable[[], Seconds]


@dataclass(frozen=True)
class StepWatch:
    """Where a step's output goes and how it is judged: its file, its progress, its listener."""

    written: BinaryIO
    progress: Progress
    on_report: Callable[[Line], None]


@dataclass
class _Heard:
    """What the pump has heard of a step: its last report's time, its quiet, its last lines."""

    started: Seconds
    last_heard: Seconds
    longest: Seconds = Seconds(0.0)
    reports: ReportCount = ReportCount(0)
    last_report: Line = Line("")
    last_line: Line = Line("")

    def line(self, line: Line, at: Seconds, progress: Progress) -> bool:
        """Take one line of output read at ``at``; answer whether it is a report."""
        self.last_line = line
        if not progress.reports(line):
            return False
        self.longest = Seconds(max(self.longest, at - self.last_heard))
        self.last_heard, self.last_report = at, line
        self.reports = ReportCount(self.reports + 1)
        return True

    def ended(self, at: Seconds, *, stalled: bool) -> Pumped:
        """Answer what was heard, the stretch since the last report counted as quiet."""
        longest = Seconds(max(self.longest, at - self.last_heard))
        return Pumped(
            stalled=stalled,
            reports=self.reports,
            longest_quiet=longest,
            last_report=self.last_report,
            last_line=self.last_line,
            ran_for=Seconds(at - self.started),
        )


def heard_line(raw: Chunk) -> Line:
    """Return one line of a step's output as its progress pattern reads it: decoded and stripped.

    A pattern therefore matches a line without the indentation its tool printed.
    """
    return Line(raw.decode("utf-8", errors="replace").strip())


def pump(output: Output, watch: StepWatch) -> Pumped:
    """Copy a step's output into its file as it comes, until it ends or stalls.

    The watch's ``on_report`` hears each report the moment it is read.
    """
    progress, now = watch.progress, output.now
    start = now()
    heard = _Heard(started=start, last_heard=start)
    pending = b""
    while True:
        deadline = None if progress.allowance is None else heard.last_heard + progress.allowance
        wait = None if deadline is None else Seconds(max(0.0, deadline - now()))
        if not output.readable_within(wait):
            if deadline is not None and now() >= deadline:
                return heard.ended(now(), stalled=True)
            continue
        chunk = output.read()
        if chunk:
            _ = watch.written.write(chunk)
            watch.written.flush()
        *complete, pending = _LINE_END.split(pending + chunk)
        if not chunk:
            complete.append(pending)
        for raw in complete:
            line = heard_line(Chunk(raw))
            if line and heard.line(line, now(), progress):
                watch.on_report(line)
        if not chunk:
            return heard.ended(now(), stalled=False)


def verdict(progress: Progress, pumped: Pumped) -> Prose:
    """Say why the watchdog stopped a step: how long it went without a report, and where it was."""
    allowance = int(progress.allowance or 0)
    return Prose(
        f"\nwatchdog: no progress report for {allowance}s; stopped."
        + f" Last report: {pumped.last_report or 'none'}. Last line: {pumped.last_line}\n"
    )


# A step that declares progress reports and runs this long without making one fails: a tool that
# stopped reporting is caught by the run that runs it.
UNREPORTED_FOR = Seconds(10.0)


def judged(progress: Progress, ran: WatchedRun, ran_for: Seconds, written: BinaryIO) -> bool:
    """Answer whether the watchdog fails a step, writing why after its output.

    A step fails when it stalled, or when it passed, declares progress reports
    and ran longer than :data:`UNREPORTED_FOR` without making one.  A step that
    failed on its own keeps its status, and its own error stays its last line.
    """
    pumped = ran.pumped
    if pumped.stalled:
        _ = written.write(str.encode(verdict(progress, pumped)))
        return True
    if ran.returncode != 0:
        return False
    if progress.expects_reports and pumped.reports == 0 and ran_for > UNREPORTED_FOR:
        said = f"\nwatchdog: the step declares progress reports and made none in {int(ran_for)}s\n"
        _ = written.write(said.encode())
        return True
    return False


# How long a stalled command, once interrupted, has to end before its group gets SIGKILL.
_GRACE = GraceSeconds(10.0)


def _a_pipe() -> tuple[Descriptor, Descriptor]:
    """Open a pipe; return its read end and its write end."""
    read, write = os.pipe()
    return Descriptor(read), Descriptor(write)


@dataclass(frozen=True)
class WatchedRun:
    """How a watched command ended: its status, and what the watchdog read of it."""

    returncode: ProcessStatus
    pumped: Pumped


def watched_output(out: Descriptor) -> Output:
    """Read the output arriving on ``out`` as the watchdog reads it, on the monotonic clock."""
    return Output(
        read=lambda: Chunk(os.read(out, 65536)),
        readable_within=lambda wait: bool(select.select([out], [], [], wait)[0]),
        now=lambda: Seconds(time.monotonic()),
    )


def run_watched(
    cmd: Sequence[CommandWord], *, cwd: Path | None, stop_fd: Descriptor | None, watch: StepWatch
) -> WatchedRun:
    """Run ``cmd`` as ``run_guarded`` does, its output read through the watchdog as it comes.

    The merged output is copied into the watch's file chunk by chunk as the
    command writes it, and its progress reports read (``tools._watchdog``).
    When the watchdog answers that the command stalled, this closes the
    guard's pipe, so the guard interrupts the command's group as it does when
    the caller dies, and copies what the command writes until it ends.
    """
    watch_read, watch_write = _a_pipe()
    watched = (watch_read,) if stop_fd is None else (watch_read, stop_fd)
    try:
        proc = subprocess.Popen(
            under_the_guard(cmd, watched, _GRACE),
            cwd=cwd,
            stdin=subprocess.DEVNULL,
            stdout=subprocess.PIPE,
            stderr=subprocess.STDOUT,
            pass_fds=watched,
            process_group=0,
        )
    finally:
        os.close(watch_read)
    guarding = True
    with proc:  # leaving the block waits for the guard, and so for the group
        try:
            # proc.stdout is not None because stdout=PIPE was requested.
            out = Descriptor(proc.stdout.fileno())  # pyright: ignore[reportOptionalMemberAccess]
            pumped = pump(watched_output(out), watch)
            if pumped.stalled:
                os.close(watch_write)  # end-of-file for the guard: it stops the group
                guarding = False
                while rest := os.read(out, 65536):
                    _ = watch.written.write(rest)
                    watch.written.flush()
        finally:
            if guarding:
                os.close(watch_write)
    return WatchedRun(ProcessStatus(proc.returncode), pumped)
