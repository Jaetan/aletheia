# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
"""``check_runtime_closure`` — the runtime-closure snapshot gate.

The gate exists because ``gen-ffi-modules`` auto-writes the cabal closure from
the import graph, so a dependency drag lands silently; only a reviewed
snapshot diff makes closure changes conscious. Per the gate-teeth rule, every
test here proves a failure mode actually fails.
"""

from __future__ import annotations

from typing import TYPE_CHECKING

from tools.check_runtime_closure import closure_modules, compare, main, proof_shaped

if TYPE_CHECKING:
    from pathlib import Path

    import pytest

CABAL_STANZA = """\
library
  other-modules:
                      MAlonzo.Code.Aletheia.Prelude
                      MAlonzo.Code.Aletheia.CAN.Frame
                      MAlonzo.RTE
  build-depends: base
"""


def _run(monkeypatch: pytest.MonkeyPatch, argv: list[str]) -> int:
    monkeypatch.setattr("sys.argv", ["check_runtime_closure", *argv])
    return main()


def _paths(tmp_path: Path, cabal: str = CABAL_STANZA) -> tuple[Path, Path]:
    cabal_p = tmp_path / "aletheia.cabal"
    _ = cabal_p.write_text(cabal, encoding="utf-8")
    return cabal_p, tmp_path / "runtime-closure.snapshot"


def test_extract_only_malonzo_code_modules() -> None:
    """MAlonzo.Code.* lines extract sorted; MAlonzo.RTE and cabal noise drop."""
    assert closure_modules(CABAL_STANZA) == [
        "MAlonzo.Code.Aletheia.CAN.Frame",
        "MAlonzo.Code.Aletheia.Prelude",
    ]


def test_proof_shaped_classification() -> None:
    """The advisory classifier flags Properties/Sound/Roundtrip names only."""
    assert proof_shaped("MAlonzo.Code.Aletheia.DBC.Properties.X")
    assert proof_shaped("MAlonzo.Code.A.Sound.Master")
    assert proof_shaped("MAlonzo.Code.A.RationalRoundtrip")
    assert not proof_shaped("MAlonzo.Code.Aletheia.DBC.Decidable.Equality")
    assert not proof_shaped("MAlonzo.Code.Aletheia.PropertiesFoo")  # sibling, not a segment


def test_compare_reports_both_directions() -> None:
    """Growth AND shrinkage both surface (a drag and a silent drop alike)."""
    added, removed = compare(["A", "B"], ["B", "C"])
    assert added == ["A"]
    assert removed == ["C"]


def test_update_then_match(tmp_path: Path, monkeypatch: pytest.MonkeyPatch) -> None:
    """--update writes the snapshot; the plain run then passes."""
    cabal, snap = _paths(tmp_path)
    assert _run(monkeypatch, ["--update", "--cabal", str(cabal), "--snapshot", str(snap)]) == 0
    assert _run(monkeypatch, ["--cabal", str(cabal), "--snapshot", str(snap)]) == 0


def test_injected_addition_fails(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch, capsys: pytest.CaptureFixture[str]
) -> None:
    """TEETH: a module added to the cabal after the snapshot must fail, classified."""
    cabal, snap = _paths(tmp_path)
    assert _run(monkeypatch, ["--update", "--cabal", str(cabal), "--snapshot", str(snap)]) == 0
    _ = cabal.write_text(
        CABAL_STANZA + "                      MAlonzo.Code.Aletheia.DBC.Properties.Phantom\n",
        encoding="utf-8",
    )
    assert _run(monkeypatch, ["--cabal", str(cabal), "--snapshot", str(snap)]) == 1
    out = capsys.readouterr().out
    assert "PROOF-SHAPED" in out
    assert "Phantom" in out


def test_removal_fails(tmp_path: Path, monkeypatch: pytest.MonkeyPatch) -> None:
    """TEETH: a module vanishing from the closure must fail too."""
    cabal, snap = _paths(tmp_path)
    assert _run(monkeypatch, ["--update", "--cabal", str(cabal), "--snapshot", str(snap)]) == 0
    shrunk = CABAL_STANZA.replace("                      MAlonzo.Code.Aletheia.CAN.Frame\n", "")
    _ = cabal.write_text(shrunk, encoding="utf-8")
    assert _run(monkeypatch, ["--cabal", str(cabal), "--snapshot", str(snap)]) == 1


def test_missing_snapshot_fails_closed(tmp_path: Path, monkeypatch: pytest.MonkeyPatch) -> None:
    """No snapshot = FAIL (fail-closed first run), not a silent pass."""
    cabal, snap = _paths(tmp_path)
    assert _run(monkeypatch, ["--cabal", str(cabal), "--snapshot", str(snap)]) == 1


def test_vacuous_cabal_could_not_check(tmp_path: Path, monkeypatch: pytest.MonkeyPatch) -> None:
    """A cabal with no MAlonzo.Code.* lines is COULD-NOT-CHECK (exit 2), never OK."""
    cabal, snap = _paths(tmp_path, cabal="library\n  build-depends: base\n")
    assert _run(monkeypatch, ["--cabal", str(cabal), "--snapshot", str(snap)]) == 2
