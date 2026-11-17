# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
"""The Python lane's shards are dealt as the witness deals them, and add up to one sweep.

``tools/mutation_python.py`` reads the stage, names each shard's report and
record, writes a shard's record from mutmut's ``.meta`` files, and holds the
shards to one whole sweep: every shard once, of the merge's commit, one census,
each having judged exactly its deal of it.  These tests plant the files a
shard leaves and hold each refusal by name.
"""

from __future__ import annotations

import json
from typing import TYPE_CHECKING

import pytest

from tools.mutation_drift import drift_for
from tools.mutation_go import Binding, ShortSha
from tools.mutation_python import (
    PYTHON_SHARDS,
    PYTHON_STAGE_ENV,
    ShardNumber,
    ShardRecord,
    dealt,
    is_python_shard,
    merge_refusal,
    python_stage,
    read_python_shards,
    read_record,
    record_python_shard,
    shard_binding,
    shard_deal,
    shard_record_name,
)
from tools.mutation_report import MutationReport
from tools.mutation_witness import Deal, MutantName, ShardCount, ShardPlace
from tools.mutation_witness import dealt as witness_dealt

from aletheia.common_types import ExitStatus, Prose

if TYPE_CHECKING:
    from collections.abc import Callable
    from pathlib import Path

# A change to the shards' records, standing for a run that went otherwise.
type _Spoil = Callable[[list[ShardRecord]], list[ShardRecord]]

_COMMIT = ShortSha("933437f2")
_CENSUS = tuple(sorted(MutantName(f"aletheia.client._ffi.x_take__mutmut_{n}") for n in range(1, 8)))


def test_the_stage_is_the_whole_lane_a_shard_or_the_merge(monkeypatch: pytest.MonkeyPatch) -> None:
    """Unset is the whole lane, a number a shard, ``merge`` the merge; anything else refused."""
    monkeypatch.delenv(PYTHON_STAGE_ENV, raising=False)
    assert python_stage() is None
    for stage, read in (("1", ShardNumber(1)), (str(PYTHON_SHARDS), ShardNumber(PYTHON_SHARDS))):
        monkeypatch.setenv(PYTHON_STAGE_ENV, stage)
        assert python_stage() == read
    monkeypatch.setenv(PYTHON_STAGE_ENV, "merge")
    assert python_stage() == "merge"
    for stage in ("0", str(PYTHON_SHARDS + 1), "one", "-1"):
        monkeypatch.setenv(PYTHON_STAGE_ENV, stage)
        with pytest.raises(
            ValueError, match=f"{PYTHON_STAGE_ENV}={stage!r} is not a shard of 1 to"
        ):
            _ = python_stage()


def test_a_shard_reports_under_a_name_of_its_own() -> None:
    """``python-<n>`` is a shard for each n of the deal, and the lane's ``python`` is not."""
    for number in range(1, PYTHON_SHARDS + 1):
        assert is_python_shard(shard_binding(ShardNumber(number)))
    for binding in ("python", f"python-{PYTHON_SHARDS + 1}", "python-0", "go-1", "python-x"):
        assert not is_python_shard(Binding(binding))
    assert shard_record_name(ShardNumber(2)) == "python-shard-2.json"
    assert shard_deal(ShardNumber(2)) == f"2/{PYTHON_SHARDS}"


def test_a_shard_is_a_leg_the_drift_gate_does_not_judge() -> None:
    """A shard's survivors are recorded; only the merge is held to the baseline."""
    shard = MutationReport(shard_binding(ShardNumber(1)), "mutmut", 10, 99, "")
    entry = drift_for(shard, {"python": {"baseline": {"survivors": 0}}})
    assert entry["status"] == "leg"


def test_the_merge_deals_as_the_witness_does() -> None:
    """The deal the merge holds each shard to is the one the witness made, shard by shard."""
    listed = [(None, name, None) for name in reversed(_CENSUS)]
    shares: list[set[MutantName]] = []
    for number in range(1, PYTHON_SHARDS + 1):
        deal = Deal(ShardPlace(number), ShardCount(PYTHON_SHARDS))
        made = sorted(name for _, name, _ in witness_dealt(listed, deal))
        assert tuple(made) == dealt(_CENSUS, ShardNumber(number))
        shares.append(set(made))
    assert set().union(*shares) == set(_CENSUS)
    assert sum(len(share) for share in shares) == len(_CENSUS)


def _meta(mutants: Path, exits: dict[MutantName, ExitStatus | None]) -> None:
    """Write mutmut's ``.meta`` for one file holding ``exits``."""
    meta = mutants / "aletheia" / "client" / "_ffi.py.meta"
    meta.parent.mkdir(parents=True, exist_ok=True)
    _ = meta.write_text(json.dumps({"exit_code_by_key": exits}), encoding="utf-8")


def _shard_exits(number: ShardNumber) -> dict[MutantName, ExitStatus | None]:
    """Return the exits a shard's sweep leaves: its deal judged, every other unchecked."""
    judged = dealt(_CENSUS, number)
    return {name: (ExitStatus(1) if name in judged else None) for name in _CENSUS}


def test_a_shard_records_its_census_and_what_it_judged(tmp_path: Path) -> None:
    """The record names every mutant made and the ones given an exit, and opens the log."""
    _meta(tmp_path / "mutants", _shard_exits(ShardNumber(1)))
    artifacts = tmp_path / "artifacts"
    artifacts.mkdir()
    header = record_python_shard(ShardNumber(1), _COMMIT, tmp_path / "mutants", artifacts)
    judged = dealt(_CENSUS, ShardNumber(1))
    assert header == f"=== Python shard 1 of {PYTHON_SHARDS}: {len(judged)} of 7 mutants ===\n"
    record = read_record(artifacts / shard_record_name(ShardNumber(1)))
    assert record == ShardRecord(ShardNumber(1), _COMMIT, _CENSUS, judged)


def test_a_shard_whose_mutmut_made_nothing_records_nothing(tmp_path: Path) -> None:
    """No ``.meta`` is no sweep, so no record is written and the caller refuses the run."""
    (tmp_path / "mutants").mkdir()
    assert record_python_shard(ShardNumber(1), _COMMIT, tmp_path / "mutants", tmp_path) is None
    assert not list(tmp_path.glob("*.json"))


def _records() -> list[ShardRecord]:
    """Every shard of one commit, each having judged its deal of the one census."""
    return [
        ShardRecord(ShardNumber(n), _COMMIT, _CENSUS, dealt(_CENSUS, ShardNumber(n)))
        for n in range(1, PYTHON_SHARDS + 1)
    ]


def test_shards_judging_their_deals_of_one_census_add_up() -> None:
    """The shards as the witness deals them are one whole sweep."""
    assert merge_refusal(_records(), _COMMIT) is None


def _first_only(records: list[ShardRecord]) -> list[ShardRecord]:
    return records[:1]


def _first_twice(records: list[ShardRecord]) -> list[ShardRecord]:
    return [records[0], *records]


def _second_elsewhere(records: list[ShardRecord]) -> list[ShardRecord]:
    return [records[0], records[1]._replace(commit=ShortSha("80ca01b9"))]


def _second_census_short(records: list[ShardRecord]) -> list[ShardRecord]:
    return [records[0], records[1]._replace(census=_CENSUS[:-1])]


def _second_judged_short(records: list[ShardRecord]) -> list[ShardRecord]:
    return [records[0], records[1]._replace(judged=records[1].judged[:-1])]


def _first_judged_over(records: list[ShardRecord]) -> list[ShardRecord]:
    judged = tuple(sorted((*records[0].judged, records[1].judged[0])))
    return [records[0]._replace(judged=judged), records[1]]


@pytest.mark.parametrize(
    ("spoil", "refusal"),
    [
        (_first_only, "the Python shards present are [1], wanted 1 to"),
        (_first_twice, "the Python shards present are [1, 1, 2]"),
        (_second_elsewhere, "Python shard 2 ran at 80ca01b9, the merge is at 933437f2"),
        (_second_census_short, "Python shards 1 and 2 read different censuses"),
        (_second_judged_short, "Python shard 2 judged 2 mutants, its deal is 3: 0 not dealt to it"),
        (_first_judged_over, "Python shard 1 judged 5 mutants, its deal is 4: 1 not dealt to it"),
    ],
    ids=["a shard missing", "a shard twice", "another commit", "another census", "short", "over"],
)
def test_each_way_the_shards_fall_short_of_one_sweep_is_refused_by_name(
    spoil: _Spoil, refusal: Prose
) -> None:
    """A missing or repeated shard, another commit or census, or a wrong deal refuses the merge."""
    found = merge_refusal(spoil(_records()), _COMMIT)
    assert found is not None
    assert found[: len(refusal)] == refusal, found


def _leave_shard(directory: Path, number: ShardNumber, error: Prose | None = None) -> None:
    """Leave what a shard's lane uploads: its record, log and report, under its own directory."""
    lane = directory / f"mutation-python-{number}" / "933437f2"
    _meta(lane / "mutants", _shard_exits(number))
    _ = record_python_shard(number, _COMMIT, lane / "mutants", lane)
    binding = shard_binding(number)
    _ = (lane / f"{binding}.raw.txt").write_text(f"log of {binding}\n", encoding="utf-8")
    _ = (lane / f"{binding}.json").write_text(json.dumps({"error": error}), encoding="utf-8")


def test_the_merge_reads_each_shard_once_wherever_the_download_put_it(tmp_path: Path) -> None:
    """Every shard's record, log and report is read; a missing or doubled file refuses."""
    for number in range(1, PYTHON_SHARDS + 1):
        _leave_shard(tmp_path, ShardNumber(number), Prose("boom") if number == 2 else None)
    parts = read_python_shards(tmp_path, _COMMIT)
    assert isinstance(parts, list)
    assert [(part.record.number, part.log, part.error) for part in parts] == [
        (ShardNumber(n), f"log of python-{n}\n", "boom" if n == 2 else None)
        for n in range(1, PYTHON_SHARDS + 1)
    ]
    other = tmp_path / "elsewhere"
    _leave_shard(other, ShardNumber(1))
    assert read_python_shards(tmp_path, _COMMIT) == (
        f"2 copies of python-shard-1.json under {tmp_path}, wanted one"
    )
    assert read_python_shards(other, _COMMIT) == (
        f"0 copies of python-shard-2.json under {other}, wanted one"
    )
    assert read_python_shards(tmp_path / "mutation-python-1", ShortSha("80ca01b9")) == (
        f"0 copies of python-shard-2.json under {tmp_path / 'mutation-python-1'}, wanted one"
    )
