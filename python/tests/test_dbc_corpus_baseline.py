# SPDX-License-Identifier: BSD-2-Clause
"""B.3 DBC text parser corpus — cantools baseline snapshot gate.

Phase B.3.a deliverable: every corpus DBC must (a) parse via the current
cantools-backed ``dbc_to_json`` without raising, and (b) produce
byte-identical output against a committed snapshot. The snapshot becomes
the structural spec the future Agda text parser is compared against in
B.3.d/B.3.e/B.3.j.

Set ``ALETHEIA_UPDATE_SNAPSHOTS=1`` to rewrite the snapshot files after an
intentional corpus change. The test fails closed otherwise.
"""

from __future__ import annotations

import json
import os
from pathlib import Path

import pytest

from aletheia.client._helpers import dump_json
from aletheia.dbc_converter import dbc_to_json

CORPUS_DIR = Path(__file__).parent / "fixtures" / "dbc_corpus"
SNAPSHOT_DIR = CORPUS_DIR / "snapshots"


def _corpus_files() -> list[Path]:
    return sorted(CORPUS_DIR.glob("*.dbc"))


def _snapshot_path(dbc_path: Path) -> Path:
    return SNAPSHOT_DIR / f"{dbc_path.stem}.json"


@pytest.mark.parametrize("dbc_path", _corpus_files(), ids=lambda p: p.name)
def test_corpus_matches_cantools_snapshot(dbc_path: Path) -> None:
    """Each corpus DBC round-trips through dbc_to_json identically to the committed snapshot.

    Pinned to ``parser="cantools"`` because this snapshot file is the
    cantools-baseline regression — the Agda parser's canonical output is
    diffed in ``test_dbc_corpus_parity.py`` against ``parity_snapshots/``,
    not against this directory.
    """
    actual = dump_json(dbc_to_json(dbc_path, parser="cantools"), indent=2) + "\n"
    snapshot = _snapshot_path(dbc_path)
    if os.environ.get("ALETHEIA_UPDATE_SNAPSHOTS") == "1":
        snapshot.parent.mkdir(parents=True, exist_ok=True)
        snapshot.write_text(actual, encoding="utf-8")
        pytest.skip(f"Updated snapshot {snapshot.name}")
    assert snapshot.exists(), (
        f"missing snapshot {snapshot}; rerun with "
        "ALETHEIA_UPDATE_SNAPSHOTS=1 to bootstrap"
    )
    expected = snapshot.read_text(encoding="utf-8")
    assert actual == expected, f"{dbc_path.name} drifted from snapshot"


def test_corpus_snapshot_files_match_corpus() -> None:
    """Every .dbc has a snapshot, and every snapshot has a .dbc — no strays."""
    dbc_stems = {p.stem for p in _corpus_files()}
    snapshot_stems = {p.stem for p in SNAPSHOT_DIR.glob("*.json")}
    assert dbc_stems == snapshot_stems, (
        f"corpus/snapshot drift: dbc-only={dbc_stems - snapshot_stems}, "
        f"snapshot-only={snapshot_stems - dbc_stems}"
    )


def test_corpus_readme_covers_every_dbc() -> None:
    """README coverage map must name every .dbc filename."""
    readme = CORPUS_DIR / "README.md"
    assert readme.exists(), "corpus README.md missing"
    text = readme.read_text(encoding="utf-8")
    for dbc in _corpus_files():
        assert dbc.name in text, f"{dbc.name} missing from corpus README"


def test_snapshot_is_valid_json() -> None:
    """Snapshot files are hand-edit-friendly — the test fails loud on bad JSON."""
    for snapshot in SNAPSHOT_DIR.glob("*.json"):
        json.loads(snapshot.read_text(encoding="utf-8"))
