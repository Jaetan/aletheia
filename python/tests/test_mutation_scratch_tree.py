# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
"""Tests for ``tools.mutation_report.scratch_tree_or_report``.

The Go and Rust lanes sweep a scratch copy of the tree through this helper,
so what is held here is its two arms: a copy it cannot make is the lane's
refusal, and only the copying is caught, an error of the sweep itself
propagating.
"""

from __future__ import annotations

from pathlib import Path

import pytest
from _git_repo import commit, git

from tools.mutation_report import MutationReport, scratch_tree_or_report


def test_a_copy_that_cannot_be_made_is_the_lanes_refusal(tmp_path: Path) -> None:
    """A directory no repository holds yields the report naming the lane and the failed step."""
    with scratch_tree_or_report(tmp_path, "go", "gremlins") as tree:
        assert isinstance(tree, MutationReport)
        assert (tree.binding, tree.tool, tree.killed, tree.survived) == ("go", "gremlins", 0, 0)
        assert tree.error is not None
        assert tree.error.startswith("no scratch copy of the tree: git worktree add")


def _failing_sweep(tree: Path | MutationReport) -> None:
    """Stand for a sweep that raises once the copy is made."""
    assert isinstance(tree, Path)
    message = "the sweep failed"
    raise RuntimeError(message)


def test_an_error_in_the_body_propagates(tmp_path: Path) -> None:
    """The sweep's own ``RuntimeError`` is not read as a copy that could not be made."""
    root = tmp_path / "repo"
    root.mkdir()
    _ = git(root, "init", "-q")
    _ = (root / "file.txt").write_text("committed\n", encoding="utf-8")
    _ = commit(root, "base")
    with (
        pytest.raises(RuntimeError, match="the sweep failed"),
        scratch_tree_or_report(root, "rust", "cargo-mutants") as tree,
    ):
        _failing_sweep(tree)
