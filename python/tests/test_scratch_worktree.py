# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
"""Tests for ``tools._common.scratch_worktree``.

A tool that edits the sources it examines works in the copy this helper
makes, so what is held here is what keeps the tree out of its reach: the
copy carries the tree as it stands, uncommitted edits included; a write in
the copy leaves the tree alone; a hook's exported git variables do not turn
the copy's commands back on this repository; and nothing is left behind,
whether the copy was made or a step refused.
"""

from __future__ import annotations

import tempfile
from typing import TYPE_CHECKING

import pytest
from _git_repo import commit, git

from tools._common import scratch_worktree

if TYPE_CHECKING:
    from pathlib import Path


@pytest.fixture(name="temp")
def _temp(tmp_path: Path, monkeypatch: pytest.MonkeyPatch) -> Path:
    """Point the temporary directory at an empty one the test can inspect."""
    temp = tmp_path / "temp"
    temp.mkdir()
    monkeypatch.setattr(tempfile, "tempdir", str(temp))
    return temp


@pytest.fixture(name="repo")
def _repo(tmp_path: Path) -> Path:
    """Return a repository with one commit, an unstaged edit and a staged one."""
    root = tmp_path / "repo"
    root.mkdir()
    _ = git(root, "init", "-q")
    _ = (root / "edited.txt").write_text("committed\n", encoding="utf-8")
    _ = (root / "staged.txt").write_text("committed\n", encoding="utf-8")
    _ = commit(root, "base")
    _ = (root / "edited.txt").write_text("unstaged edit\n", encoding="utf-8")
    _ = (root / "staged.txt").write_text("staged edit\n", encoding="utf-8")
    _ = git(root, "add", "staged.txt")
    return root.resolve()


def test_the_copy_carries_the_tree_as_it_stands(repo: Path, temp: Path) -> None:
    """HEAD with both kinds of uncommitted edit, outside the tree."""
    with scratch_worktree(repo) as tree:
        assert not tree.is_relative_to(repo)
        assert tree.is_relative_to(temp)
        assert (tree / "edited.txt").read_text(encoding="utf-8") == "unstaged edit\n"
        assert (tree / "staged.txt").read_text(encoding="utf-8") == "staged edit\n"


def test_a_write_in_the_copy_leaves_the_tree_alone(repo: Path, temp: Path) -> None:
    """The copy's files are its own, so a mutant written there never reaches the tree."""
    with scratch_worktree(repo) as tree:
        _ = (tree / "edited.txt").write_text("mutant\n", encoding="utf-8")
        assert (repo / "edited.txt").read_text(encoding="utf-8") == "unstaged edit\n"
    assert (repo / "edited.txt").read_text(encoding="utf-8") == "unstaged edit\n"
    assert not any(temp.iterdir())


def test_the_copy_is_gone_and_unregistered_on_exit(repo: Path, temp: Path) -> None:
    """Leaving the block removes the copy and its worktree entry."""
    with scratch_worktree(repo) as tree:
        assert str(tree) in git(repo, "worktree", "list", "--porcelain")
    assert not tree.exists()
    assert str(tree) not in git(repo, "worktree", "list", "--porcelain")
    assert not any(temp.iterdir())


def test_a_hooks_git_variables_do_not_reach_this_repository(
    repo: Path,
    temp: Path,
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    """Under a hook's three git variables the copy still touches nothing here."""
    staged_before = git(repo, "diff", "--cached", "--name-only")
    monkeypatch.setenv("GIT_DIR", str(repo / ".git"))
    monkeypatch.setenv("GIT_WORK_TREE", str(repo))
    monkeypatch.setenv("GIT_INDEX_FILE", str(repo / ".git" / "index"))
    with scratch_worktree(repo) as tree:
        assert (tree / "edited.txt").read_text(encoding="utf-8") == "unstaged edit\n"
    assert git(repo, "diff", "--cached", "--name-only") == staged_before
    assert (repo / "edited.txt").read_text(encoding="utf-8") == "unstaged edit\n"
    assert not any(temp.iterdir())


def test_a_work_tree_named_elsewhere_is_not_the_copys_source(
    repo: Path,
    tmp_path: Path,
    temp: Path,
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    """A ``GIT_WORK_TREE`` naming another directory does not replace the tree the copy is of."""
    elsewhere = tmp_path / "elsewhere"
    elsewhere.mkdir()
    monkeypatch.setenv("GIT_WORK_TREE", str(elsewhere))
    with scratch_worktree(repo) as tree:
        assert (tree / "edited.txt").read_text(encoding="utf-8") == "unstaged edit\n"
    assert not any(temp.iterdir())


def test_a_refused_step_is_named_and_leaves_nothing(tmp_path: Path, temp: Path) -> None:
    """A directory no repository holds is refused by name, and no copy is left."""
    outside = tmp_path / "outside"
    outside.mkdir()
    with pytest.raises(RuntimeError, match="worktree add"), scratch_worktree(outside):
        pass
    assert not any(temp.iterdir())
