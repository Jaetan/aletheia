# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
"""Tests for ``tools.docs_arms.ignored_build_trees``, the arm holding the ignore rules.

Each test plants a tree whose tracked files carry one shape: clean, one defect
of the claim, or a scan the claim expects to match and that matches nothing.
The arm is called as the gate calls it, on the tracked paths and the tracked
Markdown files, and asks git which paths the tracked rules ignore.  A tree is a
repository only where an untracked ignore file must sit where git would honour
it, the shape the arm must not be fooled by.
"""

from __future__ import annotations

from typing import TYPE_CHECKING

import pytest
from _git_repo import git
from _planted_tree import run_planted, tracked_paths

from tools._common import RelPath
from tools.docs_arms import ignored_build_trees, tracked_dirs
from tools.docs_arms.ignored_build_trees import findings

from aletheia.common_types import Prose

if TYPE_CHECKING:
    from collections.abc import Iterable
    from pathlib import Path

BUILD_FILE = RelPath("cpp/CMakeLists.txt")
CLEAN_IGNORE = Prose("build/\nbuild-asan/\n/python/.venv/\ngo/aletheia-cli\n")
CLEAN_BUILD_FILE = Prose(
    "# cmake -B build -DX=ON\n#   cmake -B build-asan -DALETHEIA_SANITIZER=address\n"
)
CLEAN_README = Prose("# Go\n\n```bash\ncd go && go build -o aletheia-cli ./cmd/aletheia\n```\n")
# Tracked sources putting top-level directories on the tree; python/ holds the sanctioned venv.
SOURCES = (
    RelPath("go/go.mod"),
    RelPath("python/pyproject.toml"),
    RelPath("rust/Cargo.toml"),
    RelPath("tools/run.py"),
)


def _repo(
    tmp_path: Path,
    *,
    ignore: Prose = CLEAN_IGNORE,
    build_file: Prose | None = CLEAN_BUILD_FILE,
    readme: Prose = CLEAN_README,
) -> Path:
    """Return a tree carrying the three files the arm reads, and ``SOURCES``, all tracked."""
    repo = tmp_path / "repo"
    repo.mkdir()
    for rel in SOURCES:
        (repo / rel).parent.mkdir(parents=True, exist_ok=True)
        _ = (repo / rel).write_text("x\n", encoding="utf-8")
    _ = (repo / ".gitignore").write_text(ignore, encoding="utf-8")
    if build_file is not None:
        (repo / "cpp").mkdir()
        _ = (repo / BUILD_FILE).write_text(build_file, encoding="utf-8")
    _ = (repo / "README.md").write_text(readme, encoding="utf-8")
    return repo


def _run(repo: Path, *, untracked: Iterable[RelPath] = ()) -> list[Prose]:
    """Call the arm as the gate does: every tracked path, every tracked Markdown file."""
    return run_planted(findings, repo, untracked=frozenset(untracked))


def test_clean_fixture_passes(tmp_path: Path) -> None:
    """Documented trees and binary ignored, the sanctioned venv ignored, no stray venv hidden."""
    assert _run(_repo(tmp_path)) == list[Prose]()


def test_documented_build_tree_not_ignored(tmp_path: Path) -> None:
    """A tree the build file tells the reader to create, absent from the ignore rules, is found."""
    repo = _repo(tmp_path, ignore=Prose("build/\n/python/.venv/\ngo/aletheia-cli\n"))
    assert _run(repo) == [
        Prose(f".gitignore: a documented build tree is not ignored: cpp/build-asan ({BUILD_FILE})")
    ]


def test_documented_go_binary_not_ignored(tmp_path: Path) -> None:
    """A Go binary a document builds from go/, absent from the ignore rules, is found."""
    repo = _repo(tmp_path, ignore=Prose("build/\nbuild-asan/\n/python/.venv/\n"))
    assert _run(repo) == [
        Prose(
            ".gitignore: a documented Go build output is not ignored: go/aletheia-cli (README.md)"
        )
    ]


def test_a_binary_two_documents_build_names_the_first(tmp_path: Path) -> None:
    """A Go build output two documents print is reported once, against the first in path order."""
    repo = _repo(tmp_path, ignore=Prose("build/\nbuild-asan/\n/python/.venv/\n"))
    _ = (repo / "A.md").write_text(CLEAN_README, encoding="utf-8")
    assert _run(repo) == [
        Prose(".gitignore: a documented Go build output is not ignored: go/aletheia-cli (A.md)")
    ]


def test_a_binary_two_documents_build_names_the_first_given(tmp_path: Path) -> None:
    """A Go build output two documents print is reported against the first in the order given."""
    repo = _repo(tmp_path, ignore=Prose("build/\nbuild-asan/\n/python/.venv/\n"))
    _ = (repo / "A.md").write_text(CLEAN_README, encoding="utf-8")
    documents = {RelPath("README.md"): CLEAN_README, RelPath("A.md"): CLEAN_README}
    assert findings(repo, tracked_paths(repo), documents) == [
        Prose(
            ".gitignore: a documented Go build output is not ignored: go/aletheia-cli (README.md)"
        )
    ]


def test_ignore_files_in_tracked_directories_answer_for_their_trees(tmp_path: Path) -> None:
    """Every tracked ignore file is asked, each in its own directory, not the top one alone."""
    repo = _repo(tmp_path, ignore=Prose("# rules live beside the trees\n"))
    nested = {
        RelPath("cpp/.gitignore"): Prose("/build/\n/build-asan/\n"),
        RelPath("go/.gitignore"): Prose("/aletheia-cli\n"),
        RelPath("python/.gitignore"): Prose("/.venv/\n"),
    }
    for rel, rules in nested.items():
        _ = (repo / rel).write_text(rules, encoding="utf-8")
    assert _run(repo) == list[Prose]()


def test_rules_ignoring_none_of_the_asked_paths_name_every_one(tmp_path: Path) -> None:
    """Rules matching no asked path are an answer: each documented path and the venv is found."""
    repo = _repo(tmp_path, ignore=Prose("# no rule\n"))
    assert _run(repo) == [
        Prose(f".gitignore: a documented build tree is not ignored: cpp/build ({BUILD_FILE})"),
        Prose(f".gitignore: a documented build tree is not ignored: cpp/build-asan ({BUILD_FILE})"),
        Prose(
            ".gitignore: a documented Go build output is not ignored: go/aletheia-cli (README.md)"
        ),
        Prose(".gitignore: the sanctioned venv is not ignored: python/.venv"),
    ]


def test_sanctioned_venv_not_ignored(tmp_path: Path) -> None:
    """The one venv the project sanctions must be ignored."""
    repo = _repo(tmp_path, ignore=Prose("build/\nbuild-asan/\ngo/aletheia-cli\n"))
    assert _run(repo) == [Prose(".gitignore: the sanctioned venv is not ignored: python/.venv")]


def _untracked_ignore_file(repo: Path, rel: RelPath, rules: Prose) -> None:
    """Make ``repo`` a repository and write ``rules`` at ``rel``, untracked.

    Untracked, as ``python -m venv`` and a local exclude leave theirs; in a
    repository, where git would honour them in the tree itself.
    """
    _ = git(repo, "init", "-q")
    path = repo / rel
    path.parent.mkdir(parents=True, exist_ok=True)
    _ = path.write_text(rules, encoding="utf-8")


@pytest.mark.parametrize(
    "local", [RelPath("python/.venv/.gitignore"), RelPath(".git/info/exclude")]
)
def test_only_the_tracked_rules_ignore_the_sanctioned_venv(tmp_path: Path, local: RelPath) -> None:
    """An untracked ignore file, the venv's own or the clone's exclude, stands in for no rule."""
    repo = _repo(tmp_path, ignore=Prose("build/\nbuild-asan/\ngo/aletheia-cli\n"))
    _untracked_ignore_file(
        repo, local, Prose("*\n" if local.endswith(".gitignore") else "/python/.venv/\n")
    )
    assert _run(repo, untracked=[local]) == [
        Prose(".gitignore: the sanctioned venv is not ignored: python/.venv")
    ]


def test_a_template_s_exclude_stands_in_for_no_rule(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    """A git template whose exclude ignores the sanctioned venv stands in for no tracked rule."""
    template = tmp_path / "template"
    (template / "info").mkdir(parents=True)
    _ = (template / "info" / "exclude").write_text("/python/.venv/\n", encoding="utf-8")
    monkeypatch.setenv("GIT_TEMPLATE_DIR", str(template))
    repo = _repo(tmp_path, ignore=Prose("build/\nbuild-asan/\ngo/aletheia-cli\n"))
    assert _run(repo) == [Prose(".gitignore: the sanctioned venv is not ignored: python/.venv")]


def test_the_user_s_global_excludes_stand_in_for_no_rule(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    """A global excludes file ignoring the sanctioned venv stands in for no tracked rule."""
    excludes = tmp_path / "excludes"
    _ = excludes.write_text("/python/.venv/\n", encoding="utf-8")
    config = tmp_path / "gitconfig"
    _ = config.write_text(f"[core]\n\texcludesFile = {excludes}\n", encoding="utf-8")
    monkeypatch.setenv("GIT_CONFIG_GLOBAL", str(config))
    repo = _repo(tmp_path, ignore=Prose("build/\nbuild-asan/\ngo/aletheia-cli\n"))
    assert _run(repo) == [Prose(".gitignore: the sanctioned venv is not ignored: python/.venv")]


def test_a_stray_venv_s_own_ignore_file_hides_it_from_no_tracked_rule(tmp_path: Path) -> None:
    """A stray venv on disk ignoring itself is not hidden by the tracked rules: no finding here."""
    repo = _repo(tmp_path)
    stray = RelPath(".venv/.gitignore")
    _untracked_ignore_file(repo, stray, Prose("*\n"))
    assert _run(repo, untracked=[stray]) == list[Prose]()


@pytest.mark.parametrize(
    "stray",
    [
        RelPath(".venv"),
        RelPath("cpp/.venv"),
        RelPath("go/.venv"),
        RelPath("rust/.venv"),
        RelPath("tools/.venv"),
    ],
)
def test_stray_venv_hidden(tmp_path: Path, stray: RelPath) -> None:
    """A venv at the top or in any top-level directory, hidden by an anchored rule, is found."""
    repo = _repo(tmp_path, ignore=Prose(f"{CLEAN_IGNORE}/{stray}/\n"))
    assert _run(repo) == [
        Prose(f".gitignore: a venv outside the sanctioned path is hidden: {stray}")
    ]


def _dirs_in_reverse_order(tracked: Iterable[RelPath]) -> list[RelPath]:
    """Return the tracked directories last path first, an order a set may iterate in."""
    return sorted(tracked_dirs(tracked), reverse=True)


def test_hidden_strays_are_named_in_path_order(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    """Every hidden stray is named in path order, whatever order the directories come in."""
    strays = [
        RelPath(".venv"),
        RelPath("cpp/.venv"),
        RelPath("go/.venv"),
        RelPath("rust/.venv"),
        RelPath("tools/.venv"),
    ]
    rules = "".join(f"/{stray}/\n" for stray in strays)
    repo = _repo(tmp_path, ignore=Prose(f"{CLEAN_IGNORE}{rules}"))
    monkeypatch.setattr(ignored_build_trees, "tracked_dirs", _dirs_in_reverse_order)
    assert _run(repo) == [
        Prose(f".gitignore: a venv outside the sanctioned path is hidden: {stray}")
        for stray in strays
    ]


def test_a_nested_directory_ignoring_its_contents_is_not_asked(tmp_path: Path) -> None:
    """Only the top and the top-level directories are asked, so a log directory's rule stands."""
    repo = _repo(tmp_path)
    log_dir = repo / "tools" / "ci-output"
    log_dir.mkdir()
    _ = (log_dir / ".gitignore").write_text("*\n!.gitignore\n", encoding="utf-8")
    assert _run(repo) == list[Prose]()


def test_build_file_documents_no_tree(tmp_path: Path) -> None:
    """A build file naming no build directory is a scan that matched nothing."""
    repo = _repo(tmp_path, build_file=Prose("project(aletheia)\n"))
    assert _run(repo) == [Prose(f"{BUILD_FILE}: the build file documents no build directory")]


def test_build_file_untracked(tmp_path: Path) -> None:
    """A tree without the C++ build file cannot document a build directory."""
    repo = _repo(tmp_path, build_file=None)
    assert _run(repo) == [
        Prose(f"{BUILD_FILE}: not tracked, so the build trees it documents are unchecked")
    ]


def test_no_document_builds_the_go_command_line(tmp_path: Path) -> None:
    """No document printing the Go build is a scan that matched nothing."""
    repo = _repo(tmp_path, readme=Prose("# Go\n\nRun the tests.\n"))
    assert _run(repo) == [
        Prose(".gitignore: no document read prints a build of the Go command line")
    ]


def test_a_tracked_build_file_the_work_tree_lacks_is_a_finding(tmp_path: Path) -> None:
    """A build file git tracks and the work tree lacks documents no tree; the rest is asked."""
    repo = _repo(tmp_path, build_file=None)
    assert run_planted(findings, repo, absent={BUILD_FILE}) == [
        Prose(f"{BUILD_FILE}: could not be read, so the build trees it documents are unchecked")
    ]


def test_a_tracked_ignore_file_the_work_tree_lacks_ends_the_asking(tmp_path: Path) -> None:
    """Rules the work tree lacks would make every answer wrong, so no path is asked."""
    repo = _repo(tmp_path)
    (repo / ".gitignore").unlink()
    assert run_planted(findings, repo, absent={RelPath(".gitignore")}) == [
        Prose(
            ".gitignore: could not be read, so no path is checked against the tracked ignore rules"
        )
    ]


def test_an_unread_ignore_file_keeps_the_findings_made_before_it(tmp_path: Path) -> None:
    """The build file's own finding stays when a nested ignore file is unread after it."""
    repo = _repo(tmp_path, build_file=Prose("# no build directory documented\n"))
    nested = RelPath("rust/.gitignore")
    assert run_planted(findings, repo, absent={nested}) == [
        Prose(f"{BUILD_FILE}: the build file documents no build directory"),
        Prose(
            f"{nested}: could not be read, so no path is checked against the tracked ignore rules"
        ),
    ]


def test_rules_with_crlf_line_ends_ignore_as_they_read(tmp_path: Path) -> None:
    """An ignore file written with CRLF line ends ignores what its lines name."""
    assert _run(_repo(tmp_path, ignore=Prose(str(CLEAN_IGNORE).replace("\n", "\r\n")))) == []


def test_rules_are_asked_as_their_bytes_a_lone_carriage_return_kept(tmp_path: Path) -> None:
    """Git keeps a lone CR inside a line, so a rule after it in that line is part of a comment.

    The rules are copied as bytes: read as text, the CR would end the comment and
    ``build/`` would be a rule of its own, ignoring a tree the tracked rules do not.
    """
    repo = _repo(tmp_path, ignore=Prose(f"# trees\r{CLEAN_IGNORE}"))
    assert _run(repo) == [
        Prose(f".gitignore: a documented build tree is not ignored: cpp/build ({BUILD_FILE})")
    ]
