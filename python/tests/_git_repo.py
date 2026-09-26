# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
"""Git setup for the tests that run a gate end to end in a throwaway repository."""

from __future__ import annotations

from typing import TYPE_CHECKING

from tools._common import find_executable, run_capture

if TYPE_CHECKING:
    from pathlib import Path


def git(repo: Path, *args: str) -> str:
    """Run a git command in ``repo``, asserting success, and return its stdout."""
    result = run_capture([find_executable("git"), "-C", str(repo), *args])
    assert result.returncode == 0, f"git {' '.join(args)} failed: {result.stderr}"
    return result.stdout


def commit(repo: Path, message: str) -> str:
    """Stage everything, commit with a local identity and no signing, return the commit hash."""
    git(repo, "add", "-A")
    git(
        repo,
        "-c",
        "user.email=test@example.com",
        "-c",
        "user.name=Test",
        "-c",
        "commit.gpgsign=false",
        "commit",
        "-q",
        "-m",
        message,
    )
    return git(repo, "rev-parse", "HEAD").strip()


def tracked_but_absent(tmp_path: Path) -> tuple[Path, str]:
    """Return a repository with one tracked file gone from the worktree, and that file's path.

    ``git ls-files`` lists the file from the index while reading it raises: the
    shape a prose gate must report as could-not-check rather than as clean.
    """
    repo = tmp_path / "repo"
    repo.mkdir()
    git(repo, "init", "-q")
    rel = "note.txt"
    _ = (repo / rel).write_text("a plain line\n", encoding="utf-8")
    git(repo, "add", "--", rel)
    (repo / rel).unlink()
    return repo, rel
