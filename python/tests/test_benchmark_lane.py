# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
"""The throughput harness runs one lane by itself, and refuses a lane it does not have.

``--lane 0`` runs every lane and ``--lane k`` the k-th alone, counted from 1,
so an instruction count of one lane holds nothing else; the other bindings'
harnesses take the flag alike.
"""

import io
import sys
from contextlib import redirect_stderr

import pytest

from benchmarks.throughput import (
    THROUGHPUT_LANES,
    LaneNumber,
    NamedBenchmark,
    parse_arguments,
    select_lane,
)


def _lanes() -> list[NamedBenchmark]:
    return [NamedBenchmark(name, float) for name in "abcdef"]


def test_lane_zero_is_every_lane() -> None:
    """Lane 0 answers the lanes as given."""
    lanes = _lanes()
    assert select_lane(lanes, LaneNumber(0)) == lanes


def test_each_lane_runs_alone() -> None:
    """Lane k answers the k-th lane and no other, the last included."""
    lanes = _lanes()
    assert len(lanes) == THROUGHPUT_LANES
    for k, lane in enumerate(lanes, start=1):
        assert select_lane(lanes, LaneNumber(k)) == [lane]


@pytest.mark.parametrize("lane", [LaneNumber(0), LaneNumber(THROUGHPUT_LANES)])
def test_a_lane_the_mode_has_is_read(monkeypatch: pytest.MonkeyPatch, lane: LaneNumber) -> None:
    """Both ends of the lanes are taken."""
    monkeypatch.setattr(sys, "argv", ["throughput", "--lane", str(lane)])
    assert parse_arguments().lane == lane


@pytest.mark.parametrize("lane", [LaneNumber(-1), LaneNumber(THROUGHPUT_LANES + 1)])
def test_a_lane_the_mode_lacks_is_refused(
    monkeypatch: pytest.MonkeyPatch, lane: LaneNumber
) -> None:
    """A lane outside 0 to 6 exits 2 naming the range and the lane asked for."""
    monkeypatch.setattr(sys, "argv", ["throughput", "--lane", str(lane)])
    errors = io.StringIO()
    with redirect_stderr(errors), pytest.raises(SystemExit) as refused:
        _ = parse_arguments()
    assert refused.value.code == 2
    assert f"--lane must be between 0 and 6, got {lane}" in errors.getvalue()
