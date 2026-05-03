# SPDX-License-Identifier: BSD-2-Clause
"""B.3.j — DBC text parser cross-binding parity gate (Python side).

**Scope.** This is a *binding-layer integration test* on a finite fixture
corpus. It does NOT extend, replace, or stand in for the universal Agda
roundtrip theorem proven in B.3.d (``∀ d → WellFormedDBC d → parseText
(formatText d) ≡ inj₂ d``, in
``Aletheia/DBC/TextParser/Properties/Substrate/Unsafe.agda``). Parser
correctness is established by that proof, universally over the DBC
domain. What this test validates instead — and why corpus-sampled
testing is the appropriate tool here, even though it would be
inappropriate as a parser-correctness proof — is that each binding's
wire-to-native conversion (Agda JSON → Python ``DBCDefinition`` /
C++ ``DbcDefinition`` / Go ``DbcDefinition``) preserves the wire bytes
faithfully. A failure here means a binding lost or mangled fields on
parse, not that the Agda parser is wrong.

Each corpus DBC parsed via the Agda-backed ``parse_dbc_text`` must
produce a byte-identical canonical JSON image against a committed
snapshot in ``fixtures/dbc_corpus/parity_snapshots/``. The same snapshots
are the oracle for the C++ (``cpp/tests/dbc_corpus_parity_tests.cpp``)
and Go (``go/aletheia/dbc_corpus_parity_test.go``) parity tests — when
all three match the same bytes, the bindings have observed identical
``DbcDefinition`` structure for every fixture.

Canonical form: ``json.dumps(..., sort_keys=True, indent=2)`` with
``FractionJSONEncoder`` + a trailing newline. Sorted keys + the
"emit int when denominator=1" rule (shared by all three bindings'
internal serializers) make the three outputs byte-identical.

Set ``ALETHEIA_UPDATE_SNAPSHOTS=1`` to refresh the parity snapshots after
an intentional Agda wire-shape change.
"""

from __future__ import annotations

import json
import os
from pathlib import Path

import pytest

from aletheia import AletheiaClient
from aletheia.client._helpers import FractionJSONEncoder

CORPUS_DIR = Path(__file__).parent / "fixtures" / "dbc_corpus"
PARITY_SNAPSHOT_DIR = CORPUS_DIR / "parity_snapshots"


def _corpus_files() -> list[Path]:
    return sorted(CORPUS_DIR.glob("*.dbc"))


def _parity_snapshot_path(dbc_path: Path) -> Path:
    return PARITY_SNAPSHOT_DIR / f"{dbc_path.stem}.json"


def _canonical_dbc_json(dbc: object) -> str:
    """Canonical JSON image of a DBC body: sorted keys, 2-space indent, trailing newline."""
    return (
        json.dumps(dbc, cls=FractionJSONEncoder, sort_keys=True, indent=2) + "\n"
    )


@pytest.mark.parametrize("dbc_path", _corpus_files(), ids=lambda p: p.name)
def test_corpus_parses_to_parity_snapshot(dbc_path: Path) -> None:
    """Each corpus DBC parsed via Agda parse_dbc_text matches its parity snapshot."""
    text = dbc_path.read_text(encoding="utf-8")
    with AletheiaClient() as client:
        resp = client.parse_dbc_text(text)
    assert resp["status"] == "success", (
        f"parse_dbc_text failed for {dbc_path.name}: {resp}"
    )
    actual = _canonical_dbc_json(resp["dbc"])
    snapshot = _parity_snapshot_path(dbc_path)
    if os.environ.get("ALETHEIA_UPDATE_SNAPSHOTS") == "1":
        snapshot.parent.mkdir(parents=True, exist_ok=True)
        snapshot.write_text(actual, encoding="utf-8")
        pytest.skip(f"Updated parity snapshot {snapshot.name}")
    assert snapshot.exists(), (
        f"missing parity snapshot {snapshot}; rerun with "
        "ALETHEIA_UPDATE_SNAPSHOTS=1 to bootstrap"
    )
    expected = snapshot.read_text(encoding="utf-8")
    assert actual == expected, (
        f"{dbc_path.name} parity drifted from snapshot — Python's "
        "parse_dbc_text output no longer matches the cross-binding oracle"
    )


def test_parity_snapshot_files_match_corpus() -> None:
    """Every .dbc has a parity snapshot, and every parity snapshot has a .dbc — no strays."""
    dbc_stems = {p.stem for p in _corpus_files()}
    snapshot_stems = {p.stem for p in PARITY_SNAPSHOT_DIR.glob("*.json")}
    assert dbc_stems == snapshot_stems, (
        f"parity-snapshot drift: dbc-only={dbc_stems - snapshot_stems}, "
        f"parity-only={snapshot_stems - dbc_stems}"
    )


def test_parity_snapshot_is_valid_json() -> None:
    """Parity snapshots are hand-edit-friendly — fail loud on bad JSON."""
    for snapshot in PARITY_SNAPSHOT_DIR.glob("*.json"):
        json.loads(snapshot.read_text(encoding="utf-8"))
