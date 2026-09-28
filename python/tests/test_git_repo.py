# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
"""Tests for the throwaway-repository helpers in ``tests/_git_repo.py``.

The suite runs from the pre-push hook, and a hook can run with git's own
variables exported, naming the repository being pushed, as one run from a
worktree does.  A helper that let them through would initialise and commit
into that repository instead of the throwaway one, so what is held here is
that the helpers build the repository they are given whatever a hook
exported.
"""

from __future__ import annotations

from typing import TYPE_CHECKING

from _git_repo import commit, git

if TYPE_CHECKING:
    from pathlib import Path

    import pytest


def test_a_hooks_repository_is_not_the_one_built(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    """Under a hook's exported git variables the commit lands in the throwaway repository."""
    decoy = tmp_path / "decoy"
    decoy.mkdir()
    _ = git(decoy, "init", "-q")
    throwaway = tmp_path / "throwaway"
    throwaway.mkdir()
    monkeypatch.setenv("GIT_DIR", str(decoy / ".git"))
    monkeypatch.setenv("GIT_WORK_TREE", str(decoy))
    monkeypatch.setenv("GIT_INDEX_FILE", str(decoy / ".git" / "index"))
    _ = git(throwaway, "init", "-q")
    _ = (throwaway / "note.txt").write_text("a line\n", encoding="utf-8")
    head = commit(throwaway, "base")
    monkeypatch.delenv("GIT_DIR")
    monkeypatch.delenv("GIT_WORK_TREE")
    monkeypatch.delenv("GIT_INDEX_FILE")
    assert git(throwaway, "rev-parse", "HEAD").strip() == head
    assert git(throwaway, "ls-files") == "note.txt\n"
    assert git(decoy, "rev-list", "--all") == ""
