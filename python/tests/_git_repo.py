# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
"""Git setup for the tests that run a gate end to end in a throwaway repository."""

from __future__ import annotations

from typing import TYPE_CHECKING

from tools._common import find_executable, git_clean_env, run_capture

if TYPE_CHECKING:
    from pathlib import Path


def git(repo: Path, *args: str) -> str:
    """Run a git command in ``repo``, asserting success, and return its stdout.

    Git runs clear of the variables a hook exports, so a suite run from a hook
    sets up its throwaway repository rather than the hook's own.
    """
    result = run_capture([find_executable("git"), "-C", str(repo), *args], env=git_clean_env())
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


def repo_with_an_uncommitted_edit(root: Path, source: Path) -> Path:
    """Return a repository at ``root`` whose ``source`` is committed, then edited and not committed.

    ``source`` is relative to ``root``: committed reading ``committed``, it
    reads ``uncommitted edit`` in the work tree, the shape a lane sweeping a
    copy of the tree as it stands must carry over.
    """
    path = root / source
    path.parent.mkdir(parents=True)
    _ = path.write_text("committed\n", encoding="utf-8")
    _ = git(root, "init", "-q")
    _ = commit(root, "base")
    _ = path.write_text("uncommitted edit\n", encoding="utf-8")
    return root.resolve()
