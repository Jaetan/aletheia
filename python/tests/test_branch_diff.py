# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
"""The branch's diff is asked of git one way, and a diff git cannot give is never an empty one.

``tools/_branch_diff.py`` is the one reading of ``git diff main...HEAD`` that the
lanes, the build step and the pin gates scope themselves by.  The git it starts
is replaced here by an answer the test writes, so what is asked and what an
answer is read as are held without a repository.
"""

from __future__ import annotations

import subprocess
from pathlib import Path
from typing import TYPE_CHECKING

from _processes import CommandWord

from tools import _branch_diff
from tools._branch_diff import BRANCH_RANGE, GitDiffOption, branch_changes, branch_diff
from tools._common import RelPath

from aletheia.common_types import ExitStatus, Prose

if TYPE_CHECKING:
    import pytest

_ROOT = Path("/repo")
_GIT = CommandWord("/usr/bin/git")


def _git_answers(
    monkeypatch: pytest.MonkeyPatch, stdout: Prose, status: ExitStatus
) -> list[list[CommandWord]]:
    """Answer every git call with ``stdout`` and ``status``; return what was asked."""
    asked: list[list[CommandWord]] = []

    def answer(cmd: list[CommandWord]) -> subprocess.CompletedProcess[Prose]:
        asked.append(cmd)
        return subprocess.CompletedProcess(cmd, status, stdout, Prose(""))

    def git(_name: CommandWord) -> CommandWord:
        return _GIT

    monkeypatch.setattr(_branch_diff, "run_capture", answer)
    monkeypatch.setattr(_branch_diff, "find_executable", git)
    return asked


def test_the_diff_is_asked_against_main_with_the_paths_last(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    """Options come before the range and the paths after ``--``, as git reads them."""
    asked = _git_answers(monkeypatch, Prose("text\n"), ExitStatus(0))
    assert branch_diff(_ROOT, GitDiffOption("-U0"), paths=(RelPath("a"), RelPath("b/"))) == "text\n"
    assert asked == [[_GIT, "-C", "/repo", "diff", "-U0", BRANCH_RANGE, "--", "a", "b/"]]


def test_with_no_paths_the_diff_carries_no_separator(monkeypatch: pytest.MonkeyPatch) -> None:
    """The whole branch is asked for when no path limits it."""
    asked = _git_answers(monkeypatch, Prose(""), ExitStatus(0))
    _ = branch_diff(_ROOT, GitDiffOption("--name-only"))
    assert asked == [[_GIT, "-C", "/repo", "diff", "--name-only", BRANCH_RANGE]]


def test_the_changed_paths_are_the_diff_s_non_empty_lines(monkeypatch: pytest.MonkeyPatch) -> None:
    """Each line git names is one path, and a branch that changed nothing is an empty list."""
    _ = _git_answers(monkeypatch, Prose("src/A.agda\n\ndocs/B.md\n"), ExitStatus(0))
    assert branch_changes(_ROOT) == [RelPath("src/A.agda"), RelPath("docs/B.md")]
    _ = _git_answers(monkeypatch, Prose(""), ExitStatus(0))
    assert branch_changes(_ROOT) == []


def test_a_diff_git_refuses_is_none(monkeypatch: pytest.MonkeyPatch) -> None:
    """No ``main`` ref or any git error is no answer, never an empty branch."""
    _ = _git_answers(monkeypatch, Prose("src/A.agda\n"), ExitStatus(128))
    assert branch_diff(_ROOT, GitDiffOption("--name-only")) is None
    assert branch_changes(_ROOT) is None


def test_without_git_the_diff_is_none(monkeypatch: pytest.MonkeyPatch, tmp_path: Path) -> None:
    """No git on the search path is no answer either."""
    monkeypatch.setenv("PATH", str(tmp_path))
    assert branch_changes(_ROOT) is None
