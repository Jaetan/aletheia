# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
"""A step's output read as it comes, its progress reports picked out, and a deadline on them.

A step reports its progress itself, in its own output: a line its
:class:`Progress` pattern matches, carrying how much of its work is done where
the tool prints a count, as ``done`` and ``total`` or as a ``percent``.
:func:`pump` copies the step's output into its file as each chunk arrives and
reads every line of it.  Each report moves the step's deadline to
``allowance`` after it; the first deadline is ``allowance`` after the step
started.  The pump waits for output only until the deadline, so nothing ticks:
when output comes it is read at once, and when the deadline passes with no
report the pump answers that the step stalled, naming its last report and its
last line.

A :class:`Progress` with no allowance holds no deadline: the pump records the
longest stretch between reports, counted from the step's start to its first
report and from its last report to its end, from which an allowance is set.

A carriage return ends a line as a newline does, since a progress bar redrawn
in place writes one per redraw.

:func:`run_watched` runs a command as ``tools._common.run_guarded`` does, its
output read through :func:`pump`, and stops its group on a stall.
"""

from __future__ import annotations

import contextlib
import os
import re
import select
import signal
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
# ends stripped; a chunk of a step's output as it arrived, or one undecoded line of it; a regular
# expression searched in a step's output or its script; how many reports a step made; the share
# of its work a report says is done, 0 to 1.
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

    ``pattern`` matches a report and, where the tool prints a count, names its
    share of the work done by the groups ``done`` and ``total`` or ``percent``;
    ``allowance`` is the most the step may go without a report, ``None`` where
    no deadline holds it, as for a step exempt from the watchdog.
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


# The pattern no line matches, and the progress of a step that reports nothing: no report of its
# moves a deadline, so its allowance, where one is set, holds it from its start.
NEVER = PatternText(r"(?!)")
NO_REPORTS_YET = Progress(NEVER)


@dataclass(frozen=True)
class Pumped:
    """What the pump read of a step: whether it stalled, and its reports.

    ``stalled`` is true when the deadline passed with no report; ``reports``
    counts them; ``longest_quiet`` is the longest stretch with none, its start
    and end included; ``last_report`` and ``last_line`` are the last of each,
    empty when there was none; ``ran_for`` is how long the pump read the step,
    from its start to its end or its stall, on the clock its output was read by.
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
    """What the pump has heard of a step: its start, its reports, its quiet, its last lines.

    ``last_heard`` is when the last report was read, the start before any.
    """

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
        at = now()
        # Checked before every wait, so output that never pauses cannot outrun the deadline.
        if deadline is not None and at >= deadline:
            # A line still unended is the step's last line but no report: its tool may yet end it.
            heard.last_line = heard_line(Chunk(pending)) or heard.last_line
            return heard.ended(at, stalled=True)
        if not output.readable_within(None if deadline is None else Seconds(deadline - at)):
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
    """Say why the watchdog stopped a step: no report in its allowance, its last report and line."""
    allowance = int(progress.allowance or 0)
    return Prose(
        f"\nwatchdog: no progress report for {allowance}s; stopped."
        + f" Last report: {pumped.last_report or 'none'}. Last line: {pumped.last_line}\n"
    )


# A step that declares progress reports and runs longer than this without making one fails: a
# tool that stopped reporting is caught by the run that runs it.
UNREPORTED_FOR = Seconds(10.0)


def judged(progress: Progress, ran: WatchedRun, ran_for: Seconds, written: BinaryIO) -> bool:
    """Answer whether the watchdog fails a step, writing why after its output.

    A step fails when it stalled, or when it passed, declares progress reports
    and ran longer than :data:`UNREPORTED_FOR` without making one.  A step that
    failed on its own without stalling keeps its status, and the watchdog
    writes no verdict after its output.
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


# How long a stalled command, once interrupted, has to end before its group gets SIGKILL, and so
# the longest its output is still read after the stall.
_GRACE = GraceSeconds(10.0)


def _a_pipe() -> tuple[Descriptor, Descriptor]:
    """Open a pipe; return its read end and its write end."""
    read, write = os.pipe()
    return Descriptor(read), Descriptor(write)


@dataclass(frozen=True)
class WatchedRun:
    """How a watched command ended: its guard's status, and what the watchdog read of it.

    ``returncode`` is the command's own status, 1 when the guard could not start it, or
    ``-SIGKILL`` once the guard was killed with its group.
    """

    returncode: ProcessStatus
    pumped: Pumped


def watched_output(out: Descriptor) -> Output:
    """Return the output arriving on ``out`` as the watchdog reads it, on the monotonic clock."""
    return Output(
        read=lambda: Chunk(os.read(out, 65536)),
        readable_within=lambda wait: bool(select.select([out], [], [], wait)[0]),
        now=lambda: Seconds(time.monotonic()),
    )


# A process group's id: its leader's process id.
ProcessGroup = NewType("ProcessGroup", int)


def _kill_group(group: ProcessGroup) -> None:
    """SIGKILL what is left of ``group``, if anything is."""
    with contextlib.suppress(ProcessLookupError):  # nothing is left
        os.killpg(group, signal.SIGKILL)


def _drain(out: Descriptor, watch: StepWatch) -> None:
    """Copy what is still written on ``out`` into the watch's file, for the guard's grace at most.

    It stops at the output's end, or once the grace has passed while something
    still holds the output open.
    """
    output = watched_output(out)
    deadline = output.now() + _GRACE
    while (left := deadline - output.now()) > 0:
        if not output.readable_within(Seconds(left)):
            continue
        if not (rest := output.read()):
            break
        _ = watch.written.write(rest)
        watch.written.flush()


def run_watched(
    cmd: Sequence[CommandWord], *, cwd: Path | None, stop_fd: Descriptor | None, watch: StepWatch
) -> WatchedRun:
    """Run ``cmd`` as ``run_guarded`` does, its output read through the watchdog as it comes.

    The merged output is copied into the watch's file chunk by chunk as the
    command writes it, and its progress reports read (``tools._watchdog``).
    On a stall this closes the guard's pipe, so a guard still running
    interrupts the command's group as it does when the caller dies; when the
    guard has already exited, this kills the group instead.  It then copies
    what is still written until the output ends or the guard's grace has
    passed, and kills what is left of the group, since a guard can exit with
    its command, just after the stall, without stopping it.  A process outside
    the group can hold the output open: what it writes after the grace is cut.
    """
    watch_read, watch_write = _a_pipe()
    watched = (watch_read,) if stop_fd is None else (watch_read, stop_fd)
    try:
        proc = subprocess.Popen(
            under_the_guard(cmd, watched, _GRACE),
            cwd=cwd,
            # Through a pipe a Python child holds what it prints in a block until the block fills,
            # so a tool's count, run-clang-tidy's ``[k/n]``, would reach the watchdog in bursts:
            # every Python child of the command writes each line as it prints it.
            env={**os.environ, "PYTHONUNBUFFERED": "1"},
            stdin=subprocess.DEVNULL,
            stdout=subprocess.PIPE,
            stderr=subprocess.STDOUT,
            pass_fds=watched,
            process_group=0,
        )
    finally:
        os.close(watch_read)
    guarding = True
    # Leaving the block waits for the guard, at most 0.25 s on KeyboardInterrupt, and so for the
    # group once the guard has stopped it.
    with proc:
        try:
            # proc.stdout is not None because stdout=PIPE was requested.
            out = Descriptor(proc.stdout.fileno())  # pyright: ignore[reportOptionalMemberAccess]
            pumped = pump(watched_output(out), watch)
            if pumped.stalled:
                os.close(watch_write)  # end-of-file for the guard: it stops the group if it runs
                guarding = False
                # The guard leads the group: once it has exited, nothing else stops what is left.
                exited = proc.poll() is not None
                if exited:
                    _kill_group(ProcessGroup(proc.pid))
                _drain(out, watch)
                if not exited:
                    # A guard whose command ends as the stall is declared exits without stopping
                    # its group; not yet reaped, its id names that group and no other.
                    _kill_group(ProcessGroup(proc.pid))
        finally:
            if guarding:
                os.close(watch_write)
    return WatchedRun(ProcessStatus(proc.returncode), pumped)
