# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
"""``tools._progress``: a tool's work reported as it walks its items, at most 21 times.

A walk reports before its first item, after each item completing another
twentieth, and after its last, so a long walk makes 21 reports and a short one
one after each item; an empty walk reports once.  Each report is printed before
the next item is handed out, and :data:`REPORT` reads its share.
"""

from __future__ import annotations

import io
from collections import deque
from typing import TYPE_CHECKING

import pytest

from tools._progress import REPORT, ItemCount, counted, report, reported
from tools._watchdog import (
    Chunk,
    Line,
    Output,
    PatternText,
    Progress,
    Seconds,
    Share,
    StepWatch,
    heard_line,
    pump,
)

from aletheia.common_types import Prose

if TYPE_CHECKING:
    from collections.abc import Iterator, Sequence

_WHAT = Prose("files")
# Our reports as the watchdog reads them.
_OURS = Progress(PatternText(REPORT))


def _reports(printed: Prose) -> list[Line]:
    return [Line(line) for line in printed.splitlines()]


def _heard(printed: Prose) -> list[Line]:
    """Answer the reports the watchdog's pump hears in ``printed``, read in one chunk."""
    chunks = deque([Chunk(printed.encode()), Chunk(b"")])
    heard: list[Line] = []
    output = Output(chunks.popleft, lambda _wait: True, lambda: Seconds(0.0))
    _ = pump(output, StepWatch(io.BytesIO(), _OURS, heard.append))
    return heard


# A twentieth of 21 items is 1.05 of them, of 59 items 2.95: the item completing each is reported.
@pytest.mark.parametrize(
    ("total", "counts"),
    [
        (ItemCount(40), range(0, 41, 2)),
        (ItemCount(21), [0, *range(2, 22)]),
        (ItemCount(59), [*range(0, 58, 3), 59]),
    ],
)
def test_a_long_walk_reports_its_start_each_twentieth_and_its_end(
    total: ItemCount, counts: Sequence[ItemCount], capsys: pytest.CaptureFixture[Prose]
) -> None:
    """A report at 0 and after each item completing another twentieth: 21, the last at the end."""
    assert list(reported(range(total), _WHAT)) == list(range(total))
    assert _reports(Prose(capsys.readouterr().err)) == [
        f"progress: {done}/{total} files" for done in counts
    ]


def test_a_short_walk_reports_after_every_item_and_an_empty_one_once(
    capsys: pytest.CaptureFixture[Prose],
) -> None:
    """Three items: a report at 0 and after each; none: a single report of 0 of 0."""
    _ = list(reported(["a", "b", "c"], _WHAT))
    assert _reports(Prose(capsys.readouterr().err)) == [
        f"progress: {done}/3 files" for done in range(4)
    ]
    _ = list(reported(list[Prose](), _WHAT))
    assert _reports(Prose(capsys.readouterr().err)) == ["progress: 0/0 files"]


def test_each_report_is_out_before_the_next_item_is_handed_out(
    capsys: pytest.CaptureFixture[Prose],
) -> None:
    """While the second item is worked on, the report the first completed is already printed."""
    seen = [_reports(Prose(capsys.readouterr().err)) for _item in reported(["a", "b"], _WHAT)]
    assert seen == [["progress: 0/2 files"], ["progress: 1/2 files"]]


def test_a_report_is_out_before_the_next_item_is_drawn(
    capsys: pytest.CaptureFixture[Prose],
) -> None:
    """A pool's results in order: the report one completes is printed before the next is drawn."""
    drawn: list[list[Line]] = []

    def results() -> Iterator[Prose]:
        for result in ("a", "b"):
            drawn.append(_reports(Prose(capsys.readouterr().err)))
            yield Prose(result)

    walk = counted(results(), ItemCount(2), _WHAT)
    handed = [_reports(Prose(capsys.readouterr().err)) for _result in walk]
    assert drawn == [["progress: 0/2 files"], ["progress: 1/2 files"]]
    assert handed == [[], []]


def test_the_report_pattern_reads_a_report_s_share() -> None:
    """:data:`REPORT` matches a report at a line's start and reads its share.

    It matches no report naming nothing, heard stripped as the watchdog hears a line.
    """
    assert _OURS.reports(Line("progress: 5/20 files"))
    assert _OURS.share(Line("progress: 5/20 files")) == Share(0.25)
    assert not _OURS.reports(Line("checking progress: 5/20 files"))
    assert not _OURS.reports(heard_line(Chunk(b"progress: 1/4 \n")))


@pytest.mark.parametrize("what", ["", "   ", "\nx", "\rx", "x\ny"])
def test_a_report_is_one_line_naming_what_it_counts(
    what: Prose, capsys: pytest.CaptureFixture[Prose]
) -> None:
    """A blank ``what``, or one holding a line end, is refused and nothing printed."""
    with pytest.raises(ValueError, match="names what it counts"):
        report(ItemCount(1), ItemCount(4), what)
    assert not capsys.readouterr().err


@pytest.mark.parametrize("what", ["x", "files loaded", "  padded  "])
def test_every_report_the_helper_prints_is_read_as_the_watchdog_hears_it(
    what: Prose, capsys: pytest.CaptureFixture[Prose]
) -> None:
    """A report the helper prints, heard as the watchdog hears a line, reads with its share.

    An empty walk's 0 of 0 is heard as a report with no share.
    """
    report(ItemCount(1), ItemCount(4), what)
    report(ItemCount(0), ItemCount(0), what)
    heard = _heard(Prose(capsys.readouterr().err))
    assert [_OURS.share(line) for line in heard] == [Share(0.25), None]
