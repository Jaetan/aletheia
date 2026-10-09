# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
"""Tests for the shake-target arm of the documentation gate (``tools/docs_arms/shake_targets.py``).

Each test plants a tree holding a Shakefile and a few documents,
then hands the arm what the gate hands it: the root, the tracked paths and the
tracked Markdown files.
"""

from __future__ import annotations

from typing import TYPE_CHECKING

import pytest
from _planted_tree import plant, run_planted

from tools._common import GateName, RelPath
from tools.docs_arms.shake_targets import findings, named_targets

from aletheia.common_types import Prose

if TYPE_CHECKING:
    from collections.abc import Mapping
    from pathlib import Path

SHAKEFILE = RelPath("Shakefile.hs")
GUIDE = RelPath("docs/development/BUILDING.md")
README = RelPath("README.md")

TWO_TARGETS = Prose(
    'main :: IO ()\nmain = shakeArgs shakeOptions $ do\n  phony "build" $ need ["lib"]\n'
    + '  phony "clean" $ removeFilesAfter "build" ["//*"]\n'
)
GUIDE_NAMING_BUILD = Prose("# Building\n\n```bash\ncabal run shake -- build\n```\n")
README_NAMING_CLEAN = Prose("# Aletheia\n\nStart over with `cabal run shake -- clean`.\n")


def _repo(tmp_path: Path, files: Mapping[RelPath, Prose]) -> Path:
    """Return a planted tree under ``tmp_path`` holding exactly ``files``."""
    return plant(tmp_path / "repo", files)


def _scan(repo: Path) -> list[Prose]:
    """Run the arm over ``repo`` the way the gate does."""
    return run_planted(findings, repo)


def test_documents_naming_defined_targets_are_clean(tmp_path: Path) -> None:
    """Every target the documents show is a phony target of the Shakefile: no finding."""
    repo = _repo(
        tmp_path, {SHAKEFILE: TWO_TARGETS, GUIDE: GUIDE_NAMING_BUILD, README: README_NAMING_CLEAN}
    )
    assert not _scan(repo)


def test_a_target_the_shakefile_lacks_is_a_finding(tmp_path: Path) -> None:
    """A fenced command naming a target the Shakefile does not define names the document."""
    guide = Prose(f"{GUIDE_NAMING_BUILD}\n```bash\ncabal run shake -- deploy\n```\n")
    repo = _repo(tmp_path, {SHAKEFILE: TWO_TARGETS, GUIDE: guide, README: README_NAMING_CLEAN})
    assert _scan(repo) == [
        Prose(
            "docs/development/BUILDING.md: names a shake target Shakefile.hs does not define: "
            + "deploy"
        )
    ]


def test_a_command_wrapped_over_two_lines_is_read(tmp_path: Path) -> None:
    """A target on the line after the separator, as a wrapped command puts it, is still read."""
    readme = Prose("# Aletheia\n\nThe sweep needs what `cabal run shake --\nbuild-all` needs.\n")
    repo = _repo(tmp_path, {SHAKEFILE: TWO_TARGETS, GUIDE: GUIDE_NAMING_BUILD, README: readme})
    assert _scan(repo) == [
        Prose("README.md: names a shake target Shakefile.hs does not define: build-all")
    ]


def test_a_command_continued_by_a_backslash_is_read(tmp_path: Path) -> None:
    """A shell command continued onto the next line by a backslash still names its target."""
    guide = Prose(f"{GUIDE_NAMING_BUILD}\n```bash\ncabal run shake -- \\\n  deploy\n```\n")
    repo = _repo(tmp_path, {SHAKEFILE: TWO_TARGETS, GUIDE: guide, README: README_NAMING_CLEAN})
    assert _scan(repo) == [
        Prose(
            "docs/development/BUILDING.md: names a shake target Shakefile.hs does not define: "
            + "deploy"
        )
    ]


@pytest.mark.parametrize(
    ("text", "expected"),
    [
        (Prose("cabal run shake --help"), set[GateName]()),
        (Prose("cabal run shake -- \\deploy"), set[GateName]()),
        (Prose("mycabal run shake -- deploy"), set[GateName]()),
        (Prose("(cabal run shake -- deploy)"), {GateName("deploy")}),
        (Prose("cabal run shake -- build2"), {GateName("build2")}),
    ],
    ids=[
        "flag-on-the-separator",
        "backslash-before-no-newline",
        "longer-word",
        "after-a-bracket",
        "digit-in-the-target",
    ],
)
def test_a_target_is_read_only_after_a_whole_separated_command(
    text: Prose, expected: set[GateName]
) -> None:
    """A flag glued to ``--``, a backslash continuing no line, or ``cabal`` inside a word: none."""
    assert named_targets(text) == expected


def test_a_hyphenated_target_the_shakefile_defines_is_clean(tmp_path: Path) -> None:
    """A phony target whose name carries a hyphen is defined, so a document may name it."""
    shakefile = Prose(f'{TWO_TARGETS}  phony "check-properties" $ need ["proofs"]\n')
    guide = Prose(f"{GUIDE_NAMING_BUILD}\n```bash\ncabal run shake -- check-properties\n```\n")
    assert not _scan(_repo(tmp_path, {SHAKEFILE: shakefile, GUIDE: guide}))


def test_a_building_guide_showing_no_shake_command_is_a_finding(tmp_path: Path) -> None:
    """The guide that keeps the build commands shows none: the scan has nothing to check."""
    guide = Prose("# Building\n\nRun the build.\n")
    repo = _repo(tmp_path, {SHAKEFILE: TWO_TARGETS, GUIDE: guide, README: README_NAMING_CLEAN})
    assert _scan(repo) == [Prose("docs/development/BUILDING.md: shows no cabal run shake command")]


def test_a_shakefile_defining_no_phony_target_is_a_finding(tmp_path: Path) -> None:
    """A Shakefile with no phony target defines nothing a document could name."""
    shakefile = Prose("main :: IO ()\nmain = shakeArgs shakeOptions $ pure ()\n")
    repo = _repo(tmp_path, {SHAKEFILE: shakefile, GUIDE: GUIDE_NAMING_BUILD})
    assert _scan(repo) == [Prose("Shakefile.hs: defines no phony target")]


def test_an_untracked_shakefile_is_a_finding(tmp_path: Path) -> None:
    """Without a tracked Shakefile, no target a document names can be checked."""
    repo = _repo(tmp_path, {GUIDE: GUIDE_NAMING_BUILD})
    assert _scan(repo) == [Prose("Shakefile.hs: not a tracked file")]
