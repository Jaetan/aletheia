# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
"""What the branch changed against ``main``, read one way for every gate scoped by it.

The mutation, coverage and benchmark lanes skip a binding the branch did not
touch, the build step re-checks its graph only when the graph moved, and the
gates holding a fact about a pinned tool run only when the pin moved.  Each asks
git the same question, ``git diff main...HEAD``: what the branch committed since
it left ``main``.  The local ``main`` ref is the one read, never ``origin/main``,
which ``actions/checkout`` is not guaranteed to create; each workflow fetches
``main`` into a local ref in a step of its own for this reading.

A diff git cannot give (no ``git`` on the search path, no ``main`` ref, any git
error) is ``None`` here, never an empty list, since an empty list is a branch
that changed nothing; each caller states what it does with either.
"""

from __future__ import annotations

from typing import TYPE_CHECKING, NewType, cast

from tools._common import RelPath, find_executable, run_capture

if TYPE_CHECKING:
    from pathlib import Path

# An option of ``git diff`` (``--name-only``, ``-U0``), and the text it prints.
GitDiffOption = NewType("GitDiffOption", str)
DiffText = NewType("DiffText", str)

# The changes since the branch left ``main``, which is the merge base's diff to
# ``HEAD``: work ``main`` gained since is not the branch's.
BRANCH_RANGE = "main...HEAD"


def branch_diff(
    repo_root: Path, *options: GitDiffOption, paths: tuple[RelPath, ...] = ()
) -> DiffText | None:
    """Return ``git diff <options> main...HEAD [-- <paths>]``, or None where git cannot give it."""
    try:
        git = find_executable("git")
    except RuntimeError:
        return None
    limit = ["--", *paths] if paths else []
    result = run_capture([git, "-C", str(repo_root), "diff", *options, BRANCH_RANGE, *limit])
    return cast("DiffText", result.stdout) if result.returncode == 0 else None


def branch_changes(repo_root: Path) -> list[RelPath] | None:
    """Return every path the branch changed against ``main``, or None where git cannot say."""
    names = branch_diff(repo_root, GitDiffOption("--name-only"))
    return None if names is None else [RelPath(line) for line in names.splitlines() if line]
