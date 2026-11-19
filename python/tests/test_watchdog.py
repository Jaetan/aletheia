# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
"""``tools._watchdog``: a step's output copied as it comes, its reports read, a deadline on them.

The pump copies every chunk into the step's file the moment it is read and
hears each report once its line ends.  A report moves the deadline to the
allowance after it, the first deadline counting from the step's start and a
line that is no report moving nothing; once the deadline passes with no report
the pump answers that the step stalled, naming its last report and last line.
With no allowance it records the longest stretch between reports, the step's
start and end included.  A carriage return ends a line, a line may arrive in
pieces, and a report's share of the work is read from its ``done`` and
``total`` or its ``percent``.  The output arrives on a scripted clock, so every
deadline is met exactly and nothing waits.
"""

from __future__ import annotations

import io
from collections import deque
from typing import TYPE_CHECKING, NamedTuple

from tools._watchdog import (
    Chunk,
    Line,
    Output,
    PatternText,
    Progress,
    Pumped,
    ReportCount,
    Seconds,
    Share,
    StepWatch,
    pump,
)

if TYPE_CHECKING:
    from collections.abc import Callable

_COUNTED = PatternText(r"\[(?P<done>\d+)/(?P<total>\d+)\]")
_PERCENT = PatternText(r"\[\s*(?P<percent>\d+)%\]")
_MINUTE = Seconds(60.0)
_CLOCK_ZERO = Seconds(0.0)


class _Arrival(NamedTuple):
    """A chunk of a step's output and the time it is ready."""

    at: Seconds
    chunk: Chunk


class _Scripted(NamedTuple):
    """A step's output on a scripted clock, and that clock's reading."""

    output: Output
    now: Callable[[], Seconds]


def _script(*arrivals: _Arrival, start: Seconds = _CLOCK_ZERO) -> _Scripted:
    """Script a step's output: each chunk ready at its time, the output ending after the last.

    The clock starts at ``start``; waiting moves it to the next chunk when it
    is ready within the wait, and by the whole wait when it is not, so a
    deadline passes exactly.
    """
    clock = [start]
    ahead = deque(arrivals)

    def now() -> Seconds:
        return clock[0]

    def readable_within(wait: Seconds | None) -> bool:
        ready = ahead[0].at if ahead else clock[0]
        if wait is not None and ready > clock[0] + wait:
            clock[0] = Seconds(clock[0] + wait)
            return False
        clock[0] = Seconds(max(clock[0], ready))
        return True

    def read() -> Chunk:
        return ahead.popleft().chunk if ahead else Chunk(b"")

    return _Scripted(Output(read, readable_within, now), now)


class _Run(NamedTuple):
    """What the pump answered, what it wrote into the step's file, the reports it heard."""

    pumped: Pumped
    written: Chunk
    heard: list[Line]


def _pumped(script: _Scripted, progress: Progress) -> _Run:
    """Pump ``script`` under ``progress``."""
    written = io.BytesIO()
    heard: list[Line] = []
    pumped = pump(script.output, StepWatch(written, progress, heard.append))
    return _Run(pumped, Chunk(written.getvalue()), heard)


def test_every_chunk_is_copied_and_every_report_heard_in_order() -> None:
    """The file holds the output byte for byte; each report is heard, the last line kept."""
    script = _script(
        _Arrival(Seconds(5.0), Chunk(b"[1/3] parse\n[2/3] che")),
        _Arrival(Seconds(9.0), Chunk(b"ck\r\n[3/3] done\nnote\n")),
    )
    run = _pumped(script, Progress(_COUNTED, _MINUTE))
    assert run.written == b"[1/3] parse\n[2/3] check\r\n[3/3] done\nnote\n"
    assert run.heard == ["[1/3] parse", "[2/3] check", "[3/3] done"]
    assert run.pumped == Pumped(
        stalled=False,
        reports=ReportCount(3),
        longest_quiet=Seconds(5.0),
        last_report=Line("[3/3] done"),
        last_line=Line("note"),
        ran_for=Seconds(9.0),
    )


def test_a_report_moves_the_deadline() -> None:
    """Reports 50 seconds apart under a 60-second allowance: no stall, however long it runs."""
    script = _script(
        *(_Arrival(Seconds(50.0 * k), Chunk(f"[{k}/4]\n".encode())) for k in range(1, 5))
    )
    run = _pumped(script, Progress(_COUNTED, _MINUTE))
    assert not run.pumped.stalled
    assert len(run.heard) == 4


def test_a_deadline_passed_with_no_report_is_a_stall_naming_the_last_report_and_line() -> None:
    """A report at 10, then only a line that is no report: stalled at 70, both named."""
    script = _script(
        _Arrival(Seconds(10.0), Chunk(b"[1/9] module A\n")),
        _Arrival(Seconds(20.0), Chunk(b"warning: slow\n")),
        _Arrival(Seconds(500.0), Chunk(b"[2/9]\n")),
    )
    run = _pumped(script, Progress(_COUNTED, _MINUTE))
    assert script.now() == 70.0
    assert run.pumped == Pumped(
        stalled=True,
        reports=ReportCount(1),
        longest_quiet=_MINUTE,
        last_report=Line("[1/9] module A"),
        last_line=Line("warning: slow"),
        ran_for=Seconds(70.0),
    )
    assert run.written == b"[1/9] module A\nwarning: slow\n"


def test_the_first_deadline_counts_from_the_start() -> None:
    """A step started at 1000 that reports only at 1500 stalls one allowance later, at 1060."""
    script = _script(
        _Arrival(Seconds(1030.0), Chunk(b"starting\n")),
        _Arrival(Seconds(1500.0), Chunk(b"[1/1]\n")),
        start=Seconds(1000.0),
    )
    run = _pumped(script, Progress(_COUNTED, _MINUTE))
    pumped = run.pumped
    assert (pumped.stalled, pumped.reports, pumped.last_report, pumped.ran_for, script.now()) == (
        True,
        ReportCount(0),
        Line(""),
        _MINUTE,
        1060.0,
    )


def test_with_no_allowance_the_longest_quiet_stretch_is_recorded_ends_included() -> None:
    """Reports at 20 and 50, the output ending at 130: the longest quiet is the last 80 seconds.

    One report at 90, the output ending at 100: it is the first 90 seconds.
    """
    script = _script(
        _Arrival(Seconds(20.0), Chunk(b"[1/2]\n")),
        _Arrival(Seconds(50.0), Chunk(b"[2/2]\n")),
        _Arrival(Seconds(130.0), Chunk(b"bye\n")),
    )
    run = _pumped(script, Progress(_COUNTED))
    assert (run.pumped.stalled, run.pumped.reports, run.pumped.longest_quiet) == (
        False,
        ReportCount(2),
        Seconds(80.0),
    )
    late = _script(
        _Arrival(Seconds(90.0), Chunk(b"[1/1]\n")), _Arrival(Seconds(100.0), Chunk(b"bye\n"))
    )
    assert _pumped(late, Progress(_COUNTED)).pumped.longest_quiet == Seconds(90.0)


def test_a_carriage_return_ends_a_line() -> None:
    """A progress bar redrawn in place is three reports, not one."""
    script = _script(_Arrival(Seconds(1.0), Chunk(b"[ 10%]\r[ 50%]\r[100%]\n")))
    run = _pumped(script, Progress(_PERCENT, _MINUTE))
    assert run.heard == ["[ 10%]", "[ 50%]", "[100%]"]


def test_a_last_line_with_no_line_end_is_read_when_the_output_ends() -> None:
    """The output's last line, unended, still counts."""
    script = _script(
        _Arrival(Seconds(1.0), Chunk(b"[1/2]\n[2/")), _Arrival(Seconds(2.0), Chunk(b"2]"))
    )
    run = _pumped(script, Progress(_COUNTED, _MINUTE))
    assert run.heard == ["[1/2]", "[2/2]"]
    assert run.pumped.last_line == "[2/2]"


def test_a_report_s_share_is_read_from_its_counts_or_its_percent() -> None:
    """done/total and percent each give a share, capped at 1; no total or no match gives none."""
    counted, percent = Progress(_COUNTED), Progress(_PERCENT)
    assert counted.share(Line("[3/12] x")) == Share(0.25)
    assert counted.share(Line("[13/12] x")) == Share(1.0)
    assert counted.share(Line("[3/0] x")) is None
    assert Progress(PatternText(r"\[(?P<done>\d+)\]")).share(Line("[3]")) is None
    assert percent.share(Line("tests [ 42%]")) == Share(0.42)
    assert percent.share(Line("[150%]")) == Share(1.0)
    assert counted.share(Line("no counts here")) is None
    assert counted.reports(Line("[1/2]"))
    assert not counted.reports(Line("1/2"))


def test_a_chunk_is_in_the_file_before_its_report_is_heard() -> None:
    """When a report is heard, the chunk carrying it is already in the file: it is never behind."""
    script = _script(
        _Arrival(Seconds(1.0), Chunk(b"[1/2]\n")), _Arrival(Seconds(2.0), Chunk(b"[2/2]\n"))
    )
    raw = io.BytesIO()
    seen: list[Chunk] = []

    def heard(_report: Line) -> None:
        seen.append(Chunk(raw.getvalue()))

    # Buffered as a step's file is: these chunks reach ``raw`` only when flushed.
    with io.BufferedWriter(raw) as written:
        _ = pump(script.output, StepWatch(written, Progress(_COUNTED, _MINUTE), heard))
    assert seen == [b"[1/2]\n", b"[1/2]\n[2/2]\n"]


def test_output_that_never_pauses_stalls_at_its_deadline() -> None:
    """A line every second, a report at 5 and no other: stalled at 15, nothing read past it.

    Output is ready at every poll and each read takes a second, so only a
    deadline tested before every wait stops the step.
    """
    clock = [Seconds(0.0)]
    ahead = deque(Chunk(b"[1/9] a\n" if k == 5 else b"noise\n") for k in range(1, 101))

    def read() -> Chunk:
        clock[0] = Seconds(clock[0] + 1.0)
        return ahead.popleft() if ahead else Chunk(b"")

    written = io.BytesIO()
    watch = StepWatch(written, Progress(_COUNTED, Seconds(10.0)), lambda _report: None)
    assert pump(Output(read, lambda _wait: True, lambda: clock[0]), watch) == Pumped(
        stalled=True,
        reports=ReportCount(1),
        longest_quiet=Seconds(10.0),
        last_report=Line("[1/9] a"),
        last_line=Line("noise"),
        ran_for=Seconds(15.0),
    )
    assert written.getvalue() == b"noise\n" * 4 + b"[1/9] a\n" + b"noise\n" * 10


def test_a_line_unended_at_a_stall_is_its_last_line_and_no_report() -> None:
    """A report, then a line unended at the deadline: its last line at the stall, and no report."""
    script = _script(
        _Arrival(Seconds(10.0), Chunk(b"[1/9] a\n[2/9] link")),
        _Arrival(Seconds(500.0), Chunk(b"ing\n")),
    )
    run = _pumped(script, Progress(_COUNTED, _MINUTE))
    assert run.pumped == Pumped(
        stalled=True,
        reports=ReportCount(1),
        longest_quiet=_MINUTE,
        last_report=Line("[1/9] a"),
        last_line=Line("[2/9] link"),
        ran_for=Seconds(70.0),
    )
    assert run.written == b"[1/9] a\n[2/9] link"
    assert run.heard == ["[1/9] a"]
