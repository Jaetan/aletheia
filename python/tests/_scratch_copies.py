# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
"""A stand-in for ``scratch_worktree``: a copy of the planted tree, made without git.

``scratch_worktree`` copies a repository's tree as it stands through git,
which ``test_scratch_worktree`` holds against a real repository.  A lane's
tests need only what the lane does with a copy: a directory holding the
tree, its own for each shard, gone once the lane leaves it.
:class:`ScratchCopies`, installed by :func:`install` as
``tools.mutation_report.scratch_worktree``, copies the planted directory to a
fresh one under its own root, records which tree each copy was asked of, and
removes the copy when the lane leaves it; ``scratch_tree_or_report`` runs
unchanged around it.
"""

from __future__ import annotations

import contextlib
import shutil
from dataclasses import dataclass, field
from pathlib import Path
from typing import TYPE_CHECKING

from tools import mutation_report

if TYPE_CHECKING:
    from collections.abc import Generator

    import pytest


@dataclass
class ScratchCopies:
    """Copies of planted trees under ``root``, each removed when its lane is done with it."""

    root: Path
    asked: list[Path] = field(default_factory=list[Path])
    made: list[Path] = field(default_factory=list[Path])

    @contextlib.contextmanager
    def __call__(self, repo_root: Path) -> Generator[Path]:
        """Yield a fresh copy of ``repo_root``, removed on exit."""
        copy = self.root / f"copy-{len(self.made)}"
        _ = shutil.copytree(repo_root, copy)
        self.asked.append(repo_root)
        self.made.append(copy)
        try:
            yield copy
        finally:
            shutil.rmtree(copy)


def install(monkeypatch: pytest.MonkeyPatch, root: Path) -> ScratchCopies:
    """Make every scratch copy of the rest of the test a plain copy under ``root``."""
    copies = ScratchCopies(root)
    monkeypatch.setattr(mutation_report, "scratch_worktree", copies)
    return copies
