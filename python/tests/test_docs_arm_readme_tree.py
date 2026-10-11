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
from _planted_tree import plant, run_planted

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
    assert _run(_repo(tmp_path, names, _tree(names))) == list[Prose]()


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
        Prose("# Title\n\n~~~\nnot-aletheia/\n├── docs/\n~~~\n"),
    ],
    ids=["no-root", "root-mid-line"],
)
def test_readme_without_a_tree_is_a_finding(tmp_path: Path, readme: Prose) -> None:
    """A README printing no tree, or a root not opening its code block, is reported, not passed."""
    repo = _repo(tmp_path, [RelPath("docs")], readme)
    assert _run(repo) == [Prose("README.md: prints no project tree")]


def test_untracked_readme_is_a_finding(tmp_path: Path) -> None:
    """A tree tracking no README.md is reported, not passed as agreeing."""
    repo = _repo(tmp_path, [RelPath("docs")], None)
    assert _run(repo) == [Prose("README.md: not tracked, so its project tree is unchecked")]


def test_a_branch_drawn_as_a_path_lists_its_top_directory(tmp_path: Path) -> None:
    """A branch such as src/Aletheia/ lists src, the first component of its path."""
    names = [RelPath("docs"), RelPath("src")]
    repo = _repo(tmp_path, names, _tree([RelPath("docs"), RelPath("src/Aletheia")]))
    assert _run(repo) == list[Prose]()


def test_a_nested_tree_lists_only_its_top_branches(tmp_path: Path) -> None:
    """A nested line drawn under a vertical bar stays in the tree and lists no directory."""
    readme = Prose(README_HEAD + "├── docs/\n│   └── guides/\n└── src/\n" + README_TAIL)
    repo = _repo(tmp_path, [RelPath("docs"), RelPath("src")], readme)
    assert _run(repo) == list[Prose]()


def test_a_spacer_line_and_a_dotted_directory_stay_in_the_tree(tmp_path: Path) -> None:
    """A bar alone on its line keeps the tree going, and a directory name may hold a dot."""
    names = [RelPath(".github"), RelPath("src")]
    readme = Prose(README_HEAD + "├── .github/\n│\n└── src/\n" + README_TAIL)
    assert _run(_repo(tmp_path, names, readme)) == list[Prose]()


def test_the_tree_is_its_whole_block_and_nothing_after_it(tmp_path: Path) -> None:
    """A branch after a note in the block is the tree's; a drawing after the block is not."""
    tree = "├── src/\n not a branch\n├── extra/\n"
    readme = Prose(README_HEAD + tree + README_TAIL + "\nother/\n└── more/\n")
    assert _run(_repo(tmp_path, [RelPath("src")], readme)) == [
        Prose("README.md: the tree lists extra/, which the repository does not track")
    ]


def test_a_root_without_branches_lists_no_directory(tmp_path: Path) -> None:
    """A code block holding the root alone is a tree that omits every tracked directory."""
    readme = Prose("# Title\n\n~~~\naletheia/\nno branches\n~~~\n")
    assert _run(_repo(tmp_path, [RelPath("docs")], readme)) == [
        Prose("README.md: the repository tracks docs/, which the tree omits")
    ]


def test_a_deep_file_counts_for_its_top_directory(tmp_path: Path) -> None:
    """A file two directories deep makes its first path component the tracked directory."""
    files = {
        RelPath("README.md"): _tree([RelPath("docs")]),
        RelPath("docs/guides/intro.txt"): Prose("intro\n"),
        RelPath("src/Aletheia/Main.agda"): Prose("module Main where\n"),
    }
    assert _run(plant(tmp_path / "repo", files)) == [
        Prose("README.md: the repository tracks src/, which the tree omits")
    ]


def test_findings_come_listed_first_then_omitted_each_in_name_order(tmp_path: Path) -> None:
    """Listed but untracked directories come first, then tracked but omitted ones, each sorted."""
    tracked = [RelPath(name) for name in ("zeta", "docs", "tools", "alpha", "lib")]
    printed = [RelPath(name) for name in ("web", "docs", "probes", "bench", "extra")]
    assert _run(_repo(tmp_path, tracked, _tree(printed))) == [
        Prose("README.md: the tree lists bench/, which the repository does not track"),
        Prose("README.md: the tree lists extra/, which the repository does not track"),
        Prose("README.md: the tree lists probes/, which the repository does not track"),
        Prose("README.md: the tree lists web/, which the repository does not track"),
        Prose("README.md: the repository tracks alpha/, which the tree omits"),
        Prose("README.md: the repository tracks lib/, which the tree omits"),
        Prose("README.md: the repository tracks tools/, which the tree omits"),
        Prose("README.md: the repository tracks zeta/, which the tree omits"),
    ]


def test_a_tracked_readme_the_work_tree_lacks_is_a_finding(tmp_path: Path) -> None:
    """A README git tracks and the work tree lacks is named as unread, never as untracked."""
    repo = _repo(tmp_path, [RelPath("docs")], None)
    readme = RelPath("README.md")
    assert run_planted(findings, repo, absent={readme}) == [
        Prose(f"{readme}: could not be read, so what it says is unchecked"),
        Prose(f"{readme}: could not be read, so its project tree is unchecked"),
    ]


def test_a_tree_outside_a_code_block_is_no_tree(tmp_path: Path) -> None:
    """The tree is a code block; the same lines written as a paragraph print no tree."""
    names = [RelPath("docs")]
    readme = Prose("# Title\n\naletheia/\n└── docs/\n")
    assert _run(_repo(tmp_path, names, readme)) == [Prose("README.md: prints no project tree")]


def test_a_tree_in_an_indented_code_block_is_read(tmp_path: Path) -> None:
    """An indented code block opening on ``aletheia/`` is the tree as much as a fence is."""
    names = [RelPath("docs")]
    readme = Prose("# Title\n\n    aletheia/\n    └── docs/\n")
    assert _run(_repo(tmp_path, names, readme)) == list[Prose]()


@pytest.mark.parametrize(
    "tree",
    [
        Prose("~~~\naletheia/\n├── docs/\n\n└── src/\n~~~\n"),
        Prose("~~~\naletheia/\n├── docs/\n(generated files omitted)\n└── src/\n~~~\n"),
        Prose("~~~\n\naletheia/  \n├── docs/\n└── src/\n~~~\n"),
        Prose("~~~\naletheia/\n├── docs/\n└── src/"),
    ],
    ids=["blank-line", "note-line", "blank-first-and-trailing-spaces", "unclosed-fence-no-newline"],
)
def test_every_branch_of_the_tree_is_read(tmp_path: Path, tree: Prose) -> None:
    """A blank or note line inside the tree cuts nothing; the root may be padded."""
    names = [RelPath("docs"), RelPath("src")]
    assert _run(_repo(tmp_path, names, Prose(f"# Title\n\n{tree}"))) == list[Prose]()


def test_a_root_away_from_the_first_column_is_no_tree(tmp_path: Path) -> None:
    """The root reads ``aletheia/`` from its line's first column."""
    readme = Prose("# Title\n\n~~~\n  aletheia/\n  ├── docs/\n~~~\n")
    assert _run(_repo(tmp_path, [RelPath("docs")], readme)) == [
        Prose("README.md: prints no project tree")
    ]


def test_a_branch_names_the_run_right_before_its_first_slash(tmp_path: Path) -> None:
    """A branch opening on a slash names nothing; ``a/b/`` names ``a``."""
    readme = Prose("# Title\n\n~~~\naletheia/\n├── /x/\n└── docs/sub/\n~~~\n")
    assert _run(_repo(tmp_path, [RelPath("docs")], readme)) == list[Prose]()


def test_an_entry_with_no_slash_is_a_file(tmp_path: Path) -> None:
    """A branch naming no ``/`` after its name is a file, not a directory."""
    readme = Prose("# Title\n\n~~~\naletheia/\n├── docs/\n└── README.md\n~~~\n")
    assert _run(_repo(tmp_path, [RelPath("docs")], readme)) == list[Prose]()
