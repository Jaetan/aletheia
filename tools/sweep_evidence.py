# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
"""Say whether a commit's tree has a passing full sweep on record.

``git push`` connects to the remote before it runs the pre-push hook, so a
sweep run inside the hook holds that connection idle for minutes, and an idle
connection that dies on the way hangs the push.  The sweep therefore runs
first and records the tree it swept.  A script that pushes asks this module
before it pushes at all; the pre-push hook asks it about the commit each
pushed ref names, and lets the push through at once when each has a record.

The tree is git's id of the tracked content as the sweep saw it: the index
with every tracked file's working copy, the content ``git ls-files`` hands
every gate, and what committing all of it would make the commit's tree.  A
sweep that ran beside an untracked file git does not ignore records no tree,
since the build may compile that file while no gate that lists the tracked
files saw it.  A sweep measures the tree again when it ends, and records one
that moved under it as moved rather than as evidence.  A record is read from
a finished log whose header and summary name the same tree and whose summary
says every step passed, the same log ``tools/check_gate_claim.py`` reads.

Usage::

    python -m tools.sweep_evidence HEAD        # HEAD's tree must have a record
    python -m tools.sweep_evidence REV...      # every revision's must

Exit 0 when every revision's tree has a record, 1 when one has none, 2 when
git cannot name a revision's tree.
"""

from __future__ import annotations

import argparse
import re
import shutil
import sys
import tempfile
from pathlib import Path
from typing import NewType, cast

from tools._common import emit, find_executable, git_clean_env, git_toplevel, run_capture
from tools.check_gate_claim import (
    LOG_DIR,
    SOURCES_UNRECORDED,
    LogLine,
    header_value,
    log_passed,
    summary_lines,
)

from aletheia.common_types import ExitStatus

# A git tree id, and a revision as the command line names it.
TreeId = NewType("TreeId", str)
Revision = NewType("Revision", str)

# The line a sweep log carries the tree on, in its header and again in its
# summary, and what it says when it vouches for no tree.  The orchestrator
# writes them through these constants, so the reader and the writer are one
# definition.
TREE_LINE = LogLine("Tree:     ")
TREE_UNRECORDED_SUBSET = SOURCES_UNRECORDED
TREE_UNRECORDED_UNTRACKED = LogLine("none (untracked files beside the tracked ones)")
TREE_MOVED = LogLine("moved during the sweep")

FOUND, MISSING, UNREADABLE = ExitStatus(0), ExitStatus(1), ExitStatus(2)
_TREE = re.compile(r"^[0-9a-f]{40}(?:[0-9a-f]{24})?$")
_GIT = find_executable("git")


def worktree_tree(repo: Path) -> TreeId | None:
    """Name the tree of the tracked content as it stands, or None beside an untracked file.

    Written through a copy of the index, so the repository's own index and
    every file in the tree are left as they were.  Git runs clear of the
    variables a hook exports, so it reads ``repo`` and no hook's repository.
    """
    clean = git_clean_env()
    others = run_capture([_GIT, "ls-files", "--others", "--exclude-standard"], cwd=repo, env=clean)
    if others.returncode != 0 or others.stdout.strip():
        return None
    index = run_capture(
        [_GIT, "rev-parse", "--path-format=absolute", "--git-path", "index"], cwd=repo, env=clean
    )
    with tempfile.TemporaryDirectory() as scratch:
        copy = Path(scratch) / "index"
        source = Path(index.stdout.strip())
        if index.returncode == 0 and source.is_file():
            _ = shutil.copyfile(source, copy)
        env = clean | {"GIT_INDEX_FILE": str(copy)}
        added = run_capture([_GIT, "add", "--update"], cwd=repo, env=env)
        written = run_capture([_GIT, "write-tree"], cwd=repo, env=env)
    tree = written.stdout.strip()
    return TreeId(tree) if added.returncode == 0 and _TREE.match(tree) else None


def tree_of(revision: Revision, repo: Path) -> TreeId | None:
    """Name a revision's tree, or None when git cannot."""
    out = run_capture(
        [_GIT, "rev-parse", "--verify", "--quiet", f"{revision}^{{tree}}"],
        cwd=repo,
        env=git_clean_env(),
    )
    tree = out.stdout.strip()
    return TreeId(tree) if out.returncode == 0 and _TREE.match(tree) else None


def recorded_tree(log: Path) -> TreeId | None:
    """Name the tree a finished log vouches for, or None when it vouches for none.

    The header and the summary must name the same tree, and the summary must
    say every step passed.
    """
    head = header_value(log, TREE_LINE)
    if head is None or not _TREE.match(head) or not log_passed(log):
        return None
    # The summary's tree is the last one the log names: a short log's tail
    # reaches back over its header too.
    tail = [
        line[len(TREE_LINE) :].strip() for line in summary_lines(log) if line.startswith(TREE_LINE)
    ]
    return TreeId(head) if tail and tail[-1] == head else None


def evidence_for(tree: TreeId, log_dir: Path) -> Path | None:
    """Name a finished log that vouches for ``tree``, or None when none does."""
    if not log_dir.is_dir():
        return None
    return next((log for log in sorted(log_dir.glob("*.log")) if recorded_tree(log) == tree), None)


def main() -> ExitStatus:
    """Report, for each revision on the command line, the log that vouches for its tree."""
    parser = argparse.ArgumentParser(description="Say whether each revision's tree was swept.")
    _ = parser.add_argument(
        "revisions", nargs="+", type=Revision, help="the revisions about to be pushed"
    )
    revisions = cast("list[Revision]", parser.parse_args().revisions)
    try:
        repo = git_toplevel(Path.cwd())
    except RuntimeError as exc:
        emit(f"sweep-evidence: {exc}")
        return UNREADABLE
    status = FOUND
    for revision in revisions:
        tree = tree_of(revision, repo)
        if tree is None:
            emit(f"sweep-evidence: git names no tree for {revision}")
            return UNREADABLE
        log = evidence_for(tree, repo / LOG_DIR)
        if log is None:
            emit(f"sweep-evidence: no passing full sweep of {revision}'s tree {tree} is on record")
            status = MISSING
        else:
            emit(f"sweep-evidence: {revision}'s tree {tree} passed in {log.relative_to(repo)}")
    return status


if __name__ == "__main__":
    sys.exit(main())
