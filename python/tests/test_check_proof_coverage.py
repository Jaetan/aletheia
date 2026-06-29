# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
"""Tests for ``tools.check_proof_coverage`` — the proof-gate exhaustiveness gate.

A hermetic end-to-end run of ``main()`` over a throwaway ``src/`` + ``Shakefile.hs``
fixture, exercising all three exit codes:

* 0 — every module is reachable from ``proofModules`` or the build roots;
* 1 — a proof module is reachable from neither (the drift this gate forbids);
* 2 — the ``proofModules`` block cannot be parsed from Shakefile.hs.

The 0/1 polarities also prove the two pieces of internal logic Copilot flagged:
the Haskell-list ``proofModules`` parser (a wrong parse drops the only root →
exit 1, or yields no roots → exit 2) and the import-closure walk (an orphan proof
module is reported only if reachability is computed correctly).  This is the
[[feedback_orchestrator_end_to_end_validation]] check at the gate level.
"""

from __future__ import annotations

from typing import TYPE_CHECKING

from tools.check_proof_coverage import main

if TYPE_CHECKING:
    from pathlib import Path

    import pytest

_SHAKEFILE_WITH_ROOTS = (
    "proofModules :: [String]\n"
    "proofModules =\n"
    '    [ "Aletheia/Bar/Properties.agda"\n'
    "    ]\n"
    "\n"
    "main :: IO ()\n"
    "main = pure ()\n"
)
_SHAKEFILE_NO_ROOTS = "module Shakefile where\n-- no proofModules list here\n"


def _write(path: Path, text: str) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(text, encoding="utf-8")


def _fixture(tmp_path: Path, *, orphan: bool, parseable: bool = True) -> Path:
    """Build a minimal repo where Main (runtime) imports Foo and Bar/Properties is a root.

    With ``orphan=True`` an Orphan/Properties proof module exists that no root
    reaches — the gap case.  With ``parseable=False`` the Shakefile has no
    ``proofModules`` list — the parse-error case.
    """
    repo = tmp_path / "repo"
    src = repo / "src" / "Aletheia"
    _write(src / "Main.agda", "open import Aletheia.Foo\n")
    _write(src / "Foo.agda", "module Aletheia.Foo where\n")
    _write(src / "Bar" / "Properties.agda", "open import Aletheia.Foo\n")
    if orphan:
        _write(src / "Orphan" / "Properties.agda", "module Aletheia.Orphan.Properties where\n")
    _write(repo / "Shakefile.hs", _SHAKEFILE_WITH_ROOTS if parseable else _SHAKEFILE_NO_ROOTS)
    return repo


def _run(repo: Path, monkeypatch: pytest.MonkeyPatch) -> int:
    monkeypatch.chdir(repo)
    return main()


def test_full_coverage_passes(tmp_path: Path, monkeypatch: pytest.MonkeyPatch) -> None:
    """Every module reachable from a root or build → exit 0."""
    assert _run(_fixture(tmp_path, orphan=False), monkeypatch) == 0


def test_uncovered_proof_module_fails(tmp_path: Path, monkeypatch: pytest.MonkeyPatch) -> None:
    """A proof module reachable from no gate root → exit 1."""
    assert _run(_fixture(tmp_path, orphan=True), monkeypatch) == 1


def test_unparseable_proofmodules_errors(tmp_path: Path, monkeypatch: pytest.MonkeyPatch) -> None:
    """A Shakefile with no proofModules list → exit 2 (parse error), not a false pass."""
    assert _run(_fixture(tmp_path, orphan=False, parseable=False), monkeypatch) == 2
