# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
"""The drift line the C++ merge prints beside its verdict (``tools.mutation_cpp.weight_drift``).

The slices are cut on the mutants each file carried when the census was last
recorded, and the surface grows without anything refusing, so the cut goes
stale quietly.  The line is the one instrument the scheduled review of those
weights reads, and nothing in the lane parses it, so its text is held here:
what the heaviest slice would carry today, against an equal share, if the
partition were cut on the recorded counts and run over the surface just swept.
The share keeps a decimal, because a census that does not divide by the slice
count otherwise prints a heaviest slice "over" a share it equals.  Three arms:
weights recorded, none recorded, and a file carrying mutants the record does
not count.
"""

from __future__ import annotations

from typing import TYPE_CHECKING

from tools import mutation_cpp
from tools._common import RelPath
from tools.mutation_cpp import weight_drift

if TYPE_CHECKING:
    from pathlib import Path

    import pytest

# Four files, three of them weighed, cut into three slices: the two heaviest
# alone, the lightest beside the one the record does not name.
_A, _B, _C, _D = (RelPath(f"cpp/src/{name}.cpp") for name in ("a", "b", "c", "d"))
_DOMAIN = [_A, _B, _C, _D]
_RECORDED = {_A: 4, _B: 4, _C: 3}


def _cut_on(monkeypatch: pytest.MonkeyPatch, recorded: dict[RelPath, int]) -> None:
    """Cut the partition on the weights given, over the fixture's domain."""

    def domain(_repo_root: Path, _config_path: Path) -> list[RelPath]:
        return list(_DOMAIN)

    monkeypatch.setattr(mutation_cpp, "recorded_mutant_counts", lambda: dict(recorded))
    monkeypatch.setattr(mutation_cpp, "slice_domain", domain)


def test_fresh_weights_read_the_share_to_a_decimal(monkeypatch: pytest.MonkeyPatch) -> None:
    """A surface that is its own record reads its heaviest slice against the exact share."""
    _cut_on(monkeypatch, _RECORDED)
    assert weight_drift(_RECORDED) == (
        "weights: the heaviest slice carries 4 of 11, 9.1% over an equal share of 3.7\n"
    )


def test_a_file_that_grew_moves_the_figure(monkeypatch: pytest.MonkeyPatch) -> None:
    """Mutants added to one recorded file land in its slice, and the line says by how much."""
    _cut_on(monkeypatch, _RECORDED)
    assert weight_drift({_A: 4, _B: 6, _C: 3}) == (
        "weights: the heaviest slice carries 6 of 13, 38.5% over an equal share of 4.3\n"
    )


def test_no_weights_recorded_is_said(monkeypatch: pytest.MonkeyPatch) -> None:
    """A record with no counts cuts the slices on nothing, and the line says so, not a figure."""
    _cut_on(monkeypatch, {})
    assert weight_drift(_RECORDED) == "weights: none recorded, so the slices are cut on nothing\n"


def test_a_file_the_record_does_not_count_is_named(monkeypatch: pytest.MonkeyPatch) -> None:
    """A file weighing nothing still lands in a slice; its mutants count there and it is named."""
    _cut_on(monkeypatch, _RECORDED)
    assert weight_drift({_A: 4, _B: 4, _C: 3, _D: 2}) == (
        "weights: the heaviest slice carries 5 of 13, 15.4% over an equal share of 4.3\n"
        "weights: 1 file(s) carry mutants the record does not count: cpp/src/d.cpp\n"
    )
