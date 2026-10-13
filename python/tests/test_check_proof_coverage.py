# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
"""Tests for ``tools.check_proof_coverage`` — the proof-gate exhaustiveness gate.

A hermetic end-to-end run of ``main()`` over a throwaway ``src/`` and build
program fixture, exercising all three exit codes:

* 0 — every module is reachable from ``proofModules`` or the build roots;
* 1 — a proof module is reachable from neither (the drift this gate forbids);
* 2 — the ``proofModules`` block cannot be parsed from the build program.

The list is found in a module under ``shake/`` as in ``Shakefile.hs``, and a
module path quoted after the list is not read as a root.  The 0/1 polarities
also prove the two pieces of internal logic:
the Haskell-list ``proofModules`` parser (a wrong parse drops the only root →
exit 1, or yields no roots → exit 2) and the import-closure walk (an orphan proof
module is reported only if reachability is computed correctly).  This is the
orchestrator end-to-end validation check at the gate level.
"""

from __future__ import annotations

from typing import TYPE_CHECKING

from tools._common import SHAKEFILE, RelPath
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


def _fixture(
    tmp_path: Path, *, orphan: bool, parseable: bool = True, source: RelPath = SHAKEFILE
) -> Path:
    """Build a minimal repo where Main (runtime) imports Foo and Bar/Properties is a root.

    With ``orphan=True`` an Orphan/Properties proof module exists that no root
    reaches — the gap case.  With ``parseable=False`` the build program has no
    ``proofModules`` list — the parse-error case.  ``source`` is the file of the
    build program the list is written in.
    """
    repo = tmp_path / "repo"
    src = repo / "src" / "Aletheia"
    _write(src / "Main.agda", "open import Aletheia.Foo\n")
    _write(src / "Foo.agda", "module Aletheia.Foo where\n")
    _write(src / "Bar" / "Properties.agda", "open import Aletheia.Foo\n")
    if orphan:
        _write(src / "Orphan" / "Properties.agda", "module Aletheia.Orphan.Properties where\n")
    if source != SHAKEFILE:
        _write(repo / SHAKEFILE, "main :: IO ()\nmain = proofRules\n")
    _write(repo / source, _SHAKEFILE_WITH_ROOTS if parseable else _SHAKEFILE_NO_ROOTS)
    return repo


def _run(repo: Path, monkeypatch: pytest.MonkeyPatch) -> int:
    monkeypatch.chdir(repo)
    monkeypatch.setattr("sys.argv", ["check_proof_coverage"])
    return main()


def test_full_coverage_passes(tmp_path: Path, monkeypatch: pytest.MonkeyPatch) -> None:
    """Every module reachable from a root or build → exit 0."""
    assert _run(_fixture(tmp_path, orphan=False), monkeypatch) == 0


def test_uncovered_proof_module_fails(tmp_path: Path, monkeypatch: pytest.MonkeyPatch) -> None:
    """A proof module reachable from no gate root → exit 1."""
    assert _run(_fixture(tmp_path, orphan=True), monkeypatch) == 1


def test_unparseable_proofmodules_errors(tmp_path: Path, monkeypatch: pytest.MonkeyPatch) -> None:
    """A build program with no proofModules list → exit 2 (parse error), not a false pass."""
    assert _run(_fixture(tmp_path, orphan=False, parseable=False), monkeypatch) == 2


def test_no_build_program_errors(tmp_path: Path, monkeypatch: pytest.MonkeyPatch) -> None:
    """A tree without Shakefile.hs → exit 2, not a pass over no roots."""
    repo = _fixture(tmp_path, orphan=False)
    (repo / "Shakefile.hs").unlink()
    assert _run(repo, monkeypatch) == 2


def test_a_list_that_never_closes_errors(tmp_path: Path, monkeypatch: pytest.MonkeyPatch) -> None:
    """A list with no closing bracket at its indent → exit 2, its quoted paths no roots."""
    repo = _fixture(tmp_path, orphan=False)
    _write(repo / "Shakefile.hs", _SHAKEFILE_WITH_ROOTS.replace("\n    ]\n", "\n  ]\n"))
    assert _run(repo, monkeypatch) == 2


def test_two_lists_error(tmp_path: Path, monkeypatch: pytest.MonkeyPatch) -> None:
    """A second definition, a stray copy in another module, → exit 2, not the first one read."""
    repo = _fixture(tmp_path, orphan=True)
    orphan_list = _SHAKEFILE_WITH_ROOTS.replace("Bar/Properties", "Orphan/Properties")
    _write(repo / "shake" / "Rules" / "Old.hs", orphan_list)
    assert _run(repo, monkeypatch) == 2


def test_list_in_a_module_under_shake_is_read(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    """The list in a module under shake/ is the list: covered → 0, an orphan → 1."""
    module = RelPath("shake/Rules/Proofs.hs")
    assert _run(_fixture(tmp_path / "a", orphan=False, source=module), monkeypatch) == 0
    assert _run(_fixture(tmp_path / "b", orphan=True, source=module), monkeypatch) == 1


def test_module_quoted_after_the_list_is_not_a_root(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    """A rule after the list, in its module, quoting the orphan's path leaves it uncovered → 1."""
    module = RelPath("shake/Rules/Proofs.hs")
    repo = _fixture(tmp_path, orphan=True, source=module)
    rule = 'proofRules = need ["Aletheia/Orphan/Properties.agda"]\n'
    _write(repo / module, _SHAKEFILE_WITH_ROOTS.partition("\nmain ")[0] + "\n" + rule)
    assert _run(repo, monkeypatch) == 1
