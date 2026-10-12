# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
"""The build program's sources, as the tools that read its rules enumerate them.

``Shakefile.hs`` and every ``.hs`` under ``shake/`` are its sources, the main
first and the modules in path order; nothing else is.  A tree without the main
is refused rather than read as a program of its modules alone, and a source
that cannot be read or is not UTF-8 is refused rather than skipped.  The real
tree registers every rule module it holds.
"""

from __future__ import annotations

import re
from pathlib import Path

import pytest

from tools._common import (
    RelPath,
    ShakeSource,
    is_shake_source,
    read_shake_program,
    shake_sources,
)

REPO = Path(__file__).resolve().parents[2]


def _plant(root: Path, files: dict[RelPath, ShakeSource]) -> None:
    for rel, text in files.items():
        path = root / rel
        path.parent.mkdir(parents=True, exist_ok=True)
        _ = path.write_text(text, encoding="utf-8")


def test_the_sources_are_the_main_and_the_modules_under_shake_in_path_order(
    tmp_path: Path,
) -> None:
    """The main first, then each module by path; a non-Haskell file under shake/ is no source."""
    _plant(
        tmp_path,
        {
            RelPath("shake/Rules/Dist.hs"): ShakeSource("dist\n"),
            RelPath("shake/Shared.hs"): ShakeSource("shared\n"),
            RelPath("shake/README.md"): ShakeSource("prose\n"),
            RelPath("Shakefile.hs"): ShakeSource("main\n"),
            RelPath("tools/Other.hs"): ShakeSource("other\n"),
        },
    )
    assert shake_sources(tmp_path) == [
        tmp_path / "Shakefile.hs",
        tmp_path / "shake/Rules/Dist.hs",
        tmp_path / "shake/Shared.hs",
    ]
    assert read_shake_program(tmp_path) == "main\n\ndist\n\nshared\n"


def test_a_tree_without_the_main_is_refused(tmp_path: Path) -> None:
    """Modules without the main are an error naming where the main was looked for."""
    _plant(tmp_path, {RelPath("shake/Rules/Dist.hs"): ShakeSource("dist\n")})
    with pytest.raises(FileNotFoundError, match=r"Shakefile\.hs"):
        _ = read_shake_program(tmp_path)


def test_a_module_that_is_not_utf8_is_refused(tmp_path: Path) -> None:
    """A source whose bytes are not UTF-8 is an error naming it, never a partial program."""
    _plant(tmp_path, {RelPath("Shakefile.hs"): ShakeSource("main\n")})
    module = tmp_path / "shake" / "Rules" / "Dist.hs"
    module.parent.mkdir(parents=True)
    _ = module.write_bytes(b"dist \xff\n")
    with pytest.raises(OSError, match=r"Dist\.hs"):
        _ = read_shake_program(tmp_path)


def test_a_module_that_cannot_be_read_is_refused(tmp_path: Path) -> None:
    """A path under shake/ named like a module that is no file is an error, not a skip."""
    _plant(tmp_path, {RelPath("Shakefile.hs"): ShakeSource("main\n")})
    (tmp_path / "shake" / "Rules" / "Dist.hs").mkdir(parents=True)
    with pytest.raises(OSError, match=r"Dist\.hs"):
        _ = read_shake_program(tmp_path)


_IMPORT = re.compile(r"^import (Rules\.\w+) \((\w+)\)$", re.MULTILINE)
_CALL = re.compile(r"^    (\w+Rules)$", re.MULTILINE)


def test_the_main_registers_every_rule_module() -> None:
    """Each module under shake/Rules is imported by the main and its rules are registered.

    The readers take a phony anywhere in the program as defined; this holds that
    every rule module the tree carries is one the main registers.
    """
    main = (REPO / "Shakefile.hs").read_text(encoding="utf-8")
    modules = {"Rules." + path.stem for path in (REPO / "shake" / "Rules").glob("*.hs")}
    imported = dict(_IMPORT.findall(main))
    assert set(imported) == modules
    assert set(_CALL.findall(main)) == set(imported.values())


@pytest.mark.parametrize(
    "rel", [RelPath("Shakefile.hs"), RelPath("shake/Shared.hs"), RelPath("shake/Rules/Dist.hs")]
)
def test_a_tracked_source_is_recognised(rel: RelPath) -> None:
    """The main and a module at any depth under shake/ are sources."""
    assert is_shake_source(rel)


@pytest.mark.parametrize(
    "rel",
    [
        RelPath("shake.cabal"),
        RelPath("shake/README.md"),
        RelPath("shakes/Rules.hs"),
        RelPath("tools/Shakefile.hs"),
        RelPath("haskell-shim/src/AletheiaFFI.hs"),
    ],
)
def test_another_file_is_not_a_source(rel: RelPath) -> None:
    """The package description, prose, a lookalike directory and other Haskell are not."""
    assert not is_shake_source(rel)
