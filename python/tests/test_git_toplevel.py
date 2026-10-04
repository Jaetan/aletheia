# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
"""Tests for ``tools._common.git_toplevel``, and for ``gate_repo_root``, a gate's use of it.

The helper answers which work tree contains a path.  Git answers a different
question when the caller's environment names the repository: a hook runs with
``GIT_DIR`` exported, and git then takes the directory it runs in as the work
tree, so a lookup anchored below the root answers the anchor itself.  The
guards build a repository with a subdirectory, set each variable that
overrides discovery, and ask from the subdirectory.
"""

from __future__ import annotations

import io
import subprocess
import sys
from typing import TYPE_CHECKING

import pytest

from tools import _common
from tools._common import GateName, find_executable, gate_repo_root, git_toplevel

if TYPE_CHECKING:
    from pathlib import Path


@pytest.fixture(name="repo")
def _repo(tmp_path: Path) -> Path:
    """Return the root of a fresh repository holding a ``sub`` directory."""
    root = tmp_path / "repo"
    (root / "sub").mkdir(parents=True)
    _ = subprocess.run(
        [find_executable("git"), "init", "-q", str(root)],
        check=True,
        capture_output=True,
    )
    return root.resolve()


def test_the_root_is_found_from_a_subdirectory(repo: Path) -> None:
    """With no override in the environment the anchor's own repository answers."""
    assert git_toplevel(repo / "sub") == repo


def test_an_exported_git_dir_does_not_move_the_root(
    repo: Path,
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    """A hook's ``GIT_DIR`` leaves the root where the anchor's path puts it."""
    monkeypatch.setenv("GIT_DIR", str(repo / ".git"))
    assert git_toplevel(repo / "sub") == repo


def test_an_exported_work_tree_does_not_move_the_root(
    repo: Path,
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    """A ``GIT_WORK_TREE`` naming another directory is not the anchor's root."""
    elsewhere = tmp_path / "elsewhere"
    elsewhere.mkdir()
    monkeypatch.setenv("GIT_WORK_TREE", str(elsewhere))
    assert git_toplevel(repo / "sub") == repo


def test_a_path_outside_any_work_tree_is_refused(tmp_path: Path) -> None:
    """An anchor no repository contains raises rather than answering."""
    outside = tmp_path / "outside"
    outside.mkdir()
    with pytest.raises(RuntimeError, match="not inside a git work tree"):
        _ = git_toplevel(outside)


def test_a_gate_gets_the_root_or_says_it_runs_outside_one(monkeypatch: pytest.MonkeyPatch) -> None:
    """Inside the repository a gate gets its root; outside, None, with the gate named."""
    assert gate_repo_root(GateName("a-gate")) == git_toplevel()

    def outside() -> Path:
        message = "not inside a git work tree"
        raise RuntimeError(message)

    errors = io.StringIO()
    monkeypatch.setattr(_common, "git_toplevel", outside)
    monkeypatch.setattr(sys, "stderr", errors)
    assert gate_repo_root(GateName("a-gate")) is None
    assert errors.getvalue() == "a-gate: not inside a git repo\n"
