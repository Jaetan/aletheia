# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
"""The project tree README.md prints names exactly the top-level directories git tracks.

A planted tree tracks a few directories and a README printing a tree; the arm
reports a listed directory the tree does not track, a tracked directory the
printed tree omits, a README printing no tree, and a tree tracking no README; a
printed tree that agrees with the tracked one yields nothing.
"""

from __future__ import annotations

from typing import TYPE_CHECKING

import pytest
from _planted_tree import run_planted

from tools._common import RelPath
from tools.docs_arms.readme_tree import findings

from aletheia.common_types import Prose

if TYPE_CHECKING:
    from collections.abc import Sequence
    from pathlib import Path


README_HEAD = "# Title\n\n## Project Structure\n\n~~~\naletheia/\n"
README_TAIL = "~~~\n\nProse after the tree.\n"


def _repo(tmp_path: Path, directories: Sequence[RelPath], readme: Prose | None) -> Path:
    """Return a planted tree tracking one file under each directory, plus ``readme``."""
    repo = tmp_path / "repo"
    repo.mkdir()
    for name in directories:
        (repo / name).mkdir()
        _ = (repo / name / "file.txt").write_text("tracked\n", encoding="utf-8")
    if readme is not None:
        _ = (repo / "README.md").write_text(readme, encoding="utf-8")
    return repo


def _tree(entries: Sequence[RelPath]) -> Prose:
    """Return a README whose tree prints ``entries`` as its directories, the last with a corner."""
    lines = [f"├── {name}/        # about {name}\n" for name in entries[:-1]]
    lines.append(f"└── {entries[-1]}/\n")
    return Prose(README_HEAD + "".join(lines) + README_TAIL)


def _run(repo: Path) -> list[Prose]:
    return run_planted(findings, repo)


def test_tree_naming_every_tracked_directory_is_clean(tmp_path: Path) -> None:
    """A tree listing exactly the tracked top-level directories is no finding."""
    names = [RelPath("docs"), RelPath("src"), RelPath("tools")]
    assert _run(_repo(tmp_path, names, _tree(names))) == []


def test_tree_omitting_a_tracked_directory_is_a_finding(tmp_path: Path) -> None:
    """A tracked top-level directory the tree does not print is reported."""
    names = [RelPath("docs"), RelPath("src"), RelPath("tools")]
    repo = _repo(tmp_path, names, _tree(names[:-1]))
    assert _run(repo) == [Prose("README.md: the repository tracks tools/, which the tree omits")]


def test_tree_listing_an_untracked_directory_is_a_finding(tmp_path: Path) -> None:
    """A directory the README prints that the tree does not track is reported."""
    names = [RelPath("docs"), RelPath("src")]
    repo = _repo(tmp_path, names, _tree([*names, RelPath("probes")]))
    assert _run(repo) == [
        Prose("README.md: the tree lists probes/, which the repository does not track")
    ]


@pytest.mark.parametrize(
    "readme",
    [
        Prose("# Title\n\nNo tree here.\n"),
        Prose("# Title\n\n~~~\naletheia/\nno branches\n~~~\n"),
        Prose("# Title\n\n~~~\nnot-aletheia/\n├── docs/\n~~~\n"),
    ],
    ids=["no-root", "root-without-branches", "root-mid-line"],
)
def test_readme_without_a_tree_is_a_finding(tmp_path: Path, readme: Prose) -> None:
    """A README printing no tree, a bare root, or a root mid-line, is reported, not passed."""
    repo = _repo(tmp_path, [RelPath("docs")], readme)
    assert _run(repo) == [Prose("README.md: prints no project tree")]


def test_untracked_readme_is_a_finding(tmp_path: Path) -> None:
    """A tree tracking no README.md is reported, not passed as agreeing."""
    repo = _repo(tmp_path, [RelPath("docs")], None)
    assert _run(repo) == [Prose("README.md: not a tracked document")]


def test_a_branch_drawn_as_a_path_lists_its_top_directory(tmp_path: Path) -> None:
    """A branch such as src/Aletheia/ lists src, the first component of its path."""
    names = [RelPath("docs"), RelPath("src")]
    repo = _repo(tmp_path, names, _tree([RelPath("docs"), RelPath("src/Aletheia")]))
    assert _run(repo) == []


def test_a_nested_tree_lists_only_its_top_branches(tmp_path: Path) -> None:
    """A nested line drawn under a vertical bar stays in the tree and lists no directory."""
    readme = Prose(README_HEAD + "├── docs/\n│   └── guides/\n└── src/\n" + README_TAIL)
    repo = _repo(tmp_path, [RelPath("docs"), RelPath("src")], readme)
    assert _run(repo) == []


def test_a_spacer_line_and_a_dotted_directory_stay_in_the_tree(tmp_path: Path) -> None:
    """A bar alone on its line keeps the tree going, and a directory name may hold a dot."""
    names = [RelPath(".github"), RelPath("src")]
    readme = Prose(README_HEAD + "├── .github/\n│\n└── src/\n" + README_TAIL)
    assert _run(_repo(tmp_path, names, readme)) == []


def test_branch_lines_after_the_tree_are_not_read(tmp_path: Path) -> None:
    """The tree ends at its first line that is not a branch; a later drawing is another tree."""
    tree = "├── src/\n not a branch\n├── extra/\n"
    readme = Prose(README_HEAD + tree + README_TAIL + "\nother/\n└── more/\n")
    assert _run(_repo(tmp_path, [RelPath("src")], readme)) == []
