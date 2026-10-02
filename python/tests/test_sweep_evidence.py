# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
"""A push asks for a passing sweep of its exact tree, and only a full, held one counts.

``tools/sweep_evidence.py`` names the tree of the tracked content a sweep saw,
and finds the finished log that vouches for a commit's tree.  Each case builds
a scratch repository, so the trees are git's own ids for real content: a
committed tree is the one the clean working tree names, an edit moves it, an
untracked file leaves no tree to name, and a log vouches only when its header
and its summary name the tree and its summary says every step passed.
"""

from __future__ import annotations

import sys
from typing import TYPE_CHECKING, NewType

from _git_repo import commit, git

from tools.check_gate_claim import LOG_DIR, LogLine
from tools.sweep_evidence import (
    FOUND,
    MISSING,
    TREE_LINE,
    TREE_MOVED,
    TREE_UNRECORDED_UNTRACKED,
    UNREADABLE,
    Revision,
    TreeId,
    evidence_for,
    main,
    recorded_tree,
    tree_of,
    worktree_tree,
)

if TYPE_CHECKING:
    from pathlib import Path

    import pytest

# A sweep log's file name.
LogName = NewType("LogName", str)

_PASSED = LogLine("Result:   ALL 3 STEPS PASSED")
_FAILED = LogLine("═══ CI FAILED — 1 step(s) failed: x ═══")


def _repo(tmp_path: Path) -> Path:
    """Build a repository with one tracked file, committed."""
    repo = tmp_path / "repo"
    repo.mkdir()
    _ = git(repo, "init", "-q")
    _ = (repo / "a.txt").write_text("one\n", encoding="utf-8")
    _ = commit(repo, "base")
    return repo


def _log(log_dir: Path, name: LogName, header: LogLine, summary: LogLine, verdict: LogLine) -> None:
    """Write a finished sweep log with the header, summary tree and verdict given."""
    log_dir.mkdir(parents=True, exist_ok=True)
    text = "\n".join(
        [
            "═══ Aletheia offline CI sweep ═══",
            f"{TREE_LINE}{header}",
            "─── a step ───",
            "═══ CI summary ═══",
            verdict,
            f"{TREE_LINE}{summary}",
            "",
        ]
    )
    _ = (log_dir / name).write_text(text, encoding="utf-8")


def test_a_clean_working_tree_names_the_commit_s_tree(tmp_path: Path) -> None:
    """With nothing edited, the tracked content is exactly HEAD's tree."""
    repo = _repo(tmp_path)
    assert worktree_tree(repo) == tree_of(Revision("HEAD"), repo)


def test_an_edit_names_the_tree_its_commit_will_have(tmp_path: Path) -> None:
    """An edited tracked file moves the tree to the one committing the edit makes."""
    repo = _repo(tmp_path)
    (repo / "a.txt").write_text("two\n", encoding="utf-8")
    edited = worktree_tree(repo)
    assert edited is not None
    assert edited != tree_of(Revision("HEAD"), repo)
    _ = commit(repo, "edit")
    assert edited == tree_of(Revision("HEAD"), repo)


def test_an_intent_added_file_is_in_the_tree_and_the_index_is_left_alone(tmp_path: Path) -> None:
    """A file added with ``-N`` is tracked, so its content is in; the real index does not move."""
    repo = _repo(tmp_path)
    (repo / "b.txt").write_text("new\n", encoding="utf-8")
    _ = git(repo, "add", "-N", "b.txt")
    staged = git(repo, "diff", "--cached", "--stat")
    tree = worktree_tree(repo)
    assert git(repo, "diff", "--cached", "--stat") == staged
    _ = commit(repo, "b")
    assert tree == tree_of(Revision("HEAD"), repo)


def test_an_untracked_file_leaves_no_tree_to_vouch_for(tmp_path: Path) -> None:
    """A file no gate lists, which the build may still compile, makes the sweep vouch for none."""
    repo = _repo(tmp_path)
    (repo / "stray.txt").write_text("stray\n", encoding="utf-8")
    assert worktree_tree(repo) is None


def test_a_log_vouches_only_for_a_full_passing_sweep_whose_tree_held(tmp_path: Path) -> None:
    """Header and summary must name the same tree, and the summary must say every step passed."""
    tree = TreeId("1" * 40)
    head = LogLine(tree)
    logs = tmp_path / "logs"
    _log(logs, LogName("held.log"), head, head, _PASSED)
    _log(logs, LogName("moved.log"), head, TREE_MOVED, _PASSED)
    _log(logs, LogName("failed.log"), head, head, _FAILED)
    _log(
        logs,
        LogName("untracked.log"),
        TREE_UNRECORDED_UNTRACKED,
        TREE_UNRECORDED_UNTRACKED,
        _PASSED,
    )
    assert recorded_tree(logs / "held.log") == tree
    assert recorded_tree(logs / "moved.log") is None
    assert recorded_tree(logs / "failed.log") is None
    assert recorded_tree(logs / "untracked.log") is None
    assert evidence_for(tree, logs) == logs / "held.log"
    assert evidence_for(TreeId("2" * 40), logs) is None
    assert evidence_for(tree, tmp_path / "absent") is None


def test_a_hook_s_git_variables_do_not_turn_git_to_another_repository(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    """Under the GIT_DIR and GIT_INDEX_FILE a hook exports, the trees named are still ``repo``'s."""
    repo = _repo(tmp_path)
    expected = TreeId(git(repo, "rev-parse", "HEAD^{tree}").strip())
    other = tmp_path / "other"
    other.mkdir()
    _ = git(other, "init", "-q")
    _ = (other / "o.txt").write_text("other\n", encoding="utf-8")
    _ = commit(other, "other")
    monkeypatch.setenv("GIT_DIR", str(other / ".git"))
    monkeypatch.setenv("GIT_INDEX_FILE", str(other / ".git" / "index"))
    assert worktree_tree(repo) == expected
    assert tree_of(Revision("HEAD"), repo) == expected


def test_the_command_says_found_missing_or_unreadable_by_its_exit(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    """Every tree on record exits 0, a tree with no record 1, a revision git cannot name 2."""
    repo = _repo(tmp_path)
    _ = (repo / ".git" / "info" / "exclude").write_text(f"{LOG_DIR}/\n", encoding="utf-8")
    head = LogLine(git(repo, "rev-parse", "HEAD^{tree}").strip())
    _log(repo / LOG_DIR, LogName("ci.log"), head, head, _PASSED)
    monkeypatch.chdir(repo)
    monkeypatch.setattr(sys, "argv", ["sweep_evidence", "HEAD"])
    assert main() == FOUND
    monkeypatch.setattr(sys, "argv", ["sweep_evidence", "HEAD", "no-such-revision"])
    assert main() == UNREADABLE
    (repo / "a.txt").write_text("two\n", encoding="utf-8")
    _ = commit(repo, "edit")
    monkeypatch.setattr(sys, "argv", ["sweep_evidence", "HEAD~1", "HEAD"])
    assert main() == MISSING
