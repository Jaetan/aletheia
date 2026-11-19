# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
"""``tools._progress``: a tool's work reported as it walks its items, at most 21 times.

A walk reports before its first item, after each item completing another
twentieth, and after its last, so a long walk makes 21 reports and a short one
one per item; an empty walk reports once.  Each report is printed before the
next item is handed out, and the pattern every reporting step declares reads
its share.
"""

from __future__ import annotations

import pytest

from tools._progress import REPORT, ItemCount, report, reported
from tools._watchdog import Chunk, Line, PatternText, Progress, Share, heard_line

from aletheia.common_types import Prose

_WHAT = Prose("files")


def _reports(printed: Prose) -> list[Line]:
    return [Line(line) for line in printed.splitlines()]


def test_a_long_walk_reports_its_start_each_twentieth_and_its_end(
    capsys: pytest.CaptureFixture[Prose],
) -> None:
    """Forty items: a report at 0 and after every second item, 21 in all."""
    assert list(reported(range(40), _WHAT)) == list(range(40))
    assert _reports(Prose(capsys.readouterr().err)) == [
        f"progress: {done}/40 files" for done in range(0, 41, 2)
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


def test_the_declared_pattern_reads_a_report_s_share() -> None:
    """Every reporting step declares :data:`REPORT`; it matches a report and reads its share."""
    declared = Progress(PatternText(REPORT))
    assert declared.reports(Line("progress: 5/20 files"))
    assert declared.share(Line("progress: 5/20 files")) == Share(0.25)
    assert not declared.reports(Line("checking progress: 5/20 files"))


@pytest.mark.parametrize("what", ["", "   "])
def test_a_report_naming_nothing_is_refused(
    what: Prose, capsys: pytest.CaptureFixture[Prose]
) -> None:
    """A report names what it counts: the watchdog hears a line stripped, and reads none bare."""
    with pytest.raises(ValueError, match="names what it counts"):
        report(ItemCount(1), ItemCount(4), what)
    assert not capsys.readouterr().err


def test_every_report_the_helper_prints_is_read_as_the_watchdog_hears_it(
    capsys: pytest.CaptureFixture[Prose],
) -> None:
    """A report the helper prints, stripped as the watchdog strips a line, reads with its share."""
    report(ItemCount(1), ItemCount(4), Prose("x"))
    heard = heard_line(Chunk(capsys.readouterr().err.encode()))
    assert Progress(PatternText(REPORT)).share(heard) == Share(0.25)
