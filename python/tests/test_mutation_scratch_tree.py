# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
"""Tests for ``tools.mutation_report.scratch_tree_or_report``.

The Go and Rust lanes sweep a scratch copy of the tree through this helper,
so what is held here is its two arms: a copy it cannot make is the lane's
refusal, and only the copying is caught, an error of the sweep itself
propagating.  The copy is ``scratch_worktree``'s own claim, so each case
stands a context manager in its place.
"""

from __future__ import annotations

import contextlib
from pathlib import Path
from typing import TYPE_CHECKING, NoReturn

import pytest

from tools.mutation_report import MutationReport, scratch_tree_or_report

from aletheia.common_types import Prose

if TYPE_CHECKING:
    from collections.abc import Generator


def _refuse(message: Prose) -> NoReturn:
    """Raise the ``RuntimeError`` ``scratch_worktree`` raises for a git step that failed."""
    raise RuntimeError(message)


def test_a_copy_that_cannot_be_made_is_the_lanes_refusal(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    """A copy git refuses yields the report naming the lane and the failed step."""
    step = f"git worktree add -q --detach {tmp_path / 'tree'} HEAD"
    refused = Prose(f"{step} failed in {tmp_path}: fatal: not a git repository")

    @contextlib.contextmanager
    def refusing(_repo_root: Path) -> Generator[Path]:
        yield _refuse(refused)

    monkeypatch.setattr("tools.mutation_report.scratch_worktree", refusing)
    with scratch_tree_or_report(tmp_path, "go", "gremlins") as tree:
        assert isinstance(tree, MutationReport)
        assert (tree.binding, tree.tool, tree.killed, tree.survived) == ("go", "gremlins", 0, 0)
        assert tree.error is not None
        assert tree.error == f"no scratch copy of the tree: {refused}"


def _failing_sweep(tree: Path | MutationReport) -> None:
    """Stand for a sweep that raises once the copy is made."""
    assert isinstance(tree, Path)
    message = "the sweep failed"
    raise RuntimeError(message)


def test_an_error_in_the_body_propagates(tmp_path: Path, monkeypatch: pytest.MonkeyPatch) -> None:
    """The sweep's own ``RuntimeError`` is not read as a copy that could not be made."""

    @contextlib.contextmanager
    def yielding(_repo_root: Path) -> Generator[Path]:
        yield tmp_path

    monkeypatch.setattr("tools.mutation_report.scratch_worktree", yielding)
    with (
        pytest.raises(RuntimeError, match="the sweep failed"),
        scratch_tree_or_report(tmp_path, "rust", "cargo-mutants") as tree,
    ):
        _failing_sweep(tree)
