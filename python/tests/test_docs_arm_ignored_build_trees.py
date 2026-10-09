# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
"""Tests for ``tools.docs_arms.ignored_build_trees``, the arm holding the ignore rules.

Each test builds a throwaway repository whose tracked files carry one shape:
clean, one defect of the claim, or a scan the claim expects to match and that
matches nothing. The arm is called as the gate calls it, on the tracked paths
and the tracked Markdown files.
"""

from __future__ import annotations

from typing import TYPE_CHECKING

import pytest
from _git_repo import commit, git

from tools._common import RelPath
from tools.check_docs import run_arm
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
    """Return a committed repository carrying the three files the arm reads, and ``SOURCES``."""
    repo = tmp_path / "repo"
    repo.mkdir()
    git(repo, "init", "-q")
    for rel in SOURCES:
        (repo / rel).parent.mkdir(parents=True, exist_ok=True)
        _ = (repo / rel).write_text("x\n", encoding="utf-8")
    _ = (repo / ".gitignore").write_text(ignore, encoding="utf-8")
    if build_file is not None:
        (repo / "cpp").mkdir()
        _ = (repo / BUILD_FILE).write_text(build_file, encoding="utf-8")
    _ = (repo / "README.md").write_text(readme, encoding="utf-8")
    _ = commit(repo, "base")
    return repo


def _run(repo: Path) -> list[Prose]:
    """Call the arm as the gate does: every tracked path, every tracked Markdown file."""
    return run_arm(findings, repo)


def test_clean_fixture_passes(tmp_path: Path) -> None:
    """Documented trees and binary ignored, the sanctioned venv ignored, no stray venv hidden."""
    assert not _run(_repo(tmp_path))


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
    _ = commit(repo, "a second document prints the build")
    assert _run(repo) == [
        Prose(".gitignore: a documented Go build output is not ignored: go/aletheia-cli (A.md)")
    ]


def test_sanctioned_venv_not_ignored(tmp_path: Path) -> None:
    """The one venv the project sanctions must be ignored."""
    repo = _repo(tmp_path, ignore=Prose("build/\nbuild-asan/\ngo/aletheia-cli\n"))
    assert _run(repo) == [Prose(".gitignore: the sanctioned venv is not ignored: python/.venv")]


def _untracked_ignore_file(repo: Path, rel: RelPath, rules: Prose) -> None:
    """Write ``rules`` at ``rel`` after the commit, as ``python -m venv`` and a local exclude do."""
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
    assert _run(repo) == [Prose(".gitignore: the sanctioned venv is not ignored: python/.venv")]


def test_a_stray_venv_s_own_ignore_file_hides_it_from_no_tracked_rule(tmp_path: Path) -> None:
    """A stray venv on disk ignoring itself is not hidden by the tracked rules: no finding here."""
    repo = _repo(tmp_path)
    _untracked_ignore_file(repo, RelPath(".venv/.gitignore"), Prose("*\n"))
    assert not _run(repo)


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
    _ = commit(repo, "a log directory ignoring its contents")
    assert not _run(repo)


def test_build_file_documents_no_tree(tmp_path: Path) -> None:
    """A build file naming no build directory is a scan that matched nothing."""
    repo = _repo(tmp_path, build_file=Prose("project(aletheia)\n"))
    assert _run(repo) == [Prose(f"{BUILD_FILE}: the build file documents no build directory")]


def test_build_file_untracked(tmp_path: Path) -> None:
    """A tree without the C++ build file cannot document a build directory."""
    repo = _repo(tmp_path, build_file=None)
    assert _run(repo) == [Prose(f"{BUILD_FILE}: the C++ build file is not tracked")]


def test_no_document_builds_the_go_command_line(tmp_path: Path) -> None:
    """No document printing the Go build is a scan that matched nothing."""
    repo = _repo(tmp_path, readme=Prose("# Go\n\nRun the tests.\n"))
    assert _run(repo) == [
        Prose(".gitignore: no tracked document prints a build of the Go command line")
    ]
