# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
"""A ``tools.run_ci.Runner`` over a scratch tree, its measures taken without git.

The sweep digests the build sources it observes before its steps run and
again once they passed, and names the tree it swept the same way; both
measures are git's in the tool.  Here they are read from the scratch tree's
files: :func:`sources_of` and :func:`tree_of` move exactly when a step writes
what git's measures would see move, and :func:`measured_in_process` has the
sweep take its second reading through them.  Each step's command is answered
by a stand-in from ``_step_runs``.
"""

from __future__ import annotations

import hashlib
from typing import TYPE_CHECKING, NewType

from _processes import CommandWord
from _step_runs import StepRuns, ends, install, passes

from tools import run_ci
from tools._common import RelPath
from tools._run_ci_options import OptInLanes, OptInOptions
from tools.check_gate_claim import is_build_source
from tools.run_ci import RunContext, Runner
from tools.sweep_evidence import TreeId

from aletheia.common_types import ExitStatus

if TYPE_CHECKING:
    from pathlib import Path

    import pytest

    from tools._run_ci_options import LaneName

# The digest of the build sources a sweep observes, as its header records it.
SourcesDigest = NewType("SourcesDigest", str)

# The step commands most tests register, as the shell would read them.
EXIT_0 = CommandWord("exit 0")
EXIT_1 = CommandWord("exit 1")

# The interpreter a scratch runner names for its Python steps.
_PYTHON = CommandWord("python3")


def sources_of(repo: Path) -> SourcesDigest:
    """Digest the build sources under ``repo`` by path and content, without git.

    Stands in for ``sources_digest_of_worktree``, whose listing and hashing are
    git's: a step that writes a build source moves this digest as it moves that
    one, and nothing else does.
    """
    entries = sorted(
        (rel, hashlib.sha256(path.read_bytes()).hexdigest())
        for path in repo.rglob("*")
        if path.is_file() and is_build_source(rel := RelPath(path.relative_to(repo).as_posix()))
    )
    return SourcesDigest(hashlib.sha256(repr(entries).encode()).hexdigest())


def tree_of(repo: Path) -> TreeId:
    """Name the tree of ``repo``'s one tracked file, ``a.txt``, by its content, without git.

    Stands in for ``worktree_tree``: an edit of the file moves the name, as it
    moves the tree git would write.
    """
    return TreeId(hashlib.sha256((repo / "a.txt").read_bytes()).hexdigest())


def measured_in_process(monkeypatch: pytest.MonkeyPatch) -> None:
    """Have the sweep re-measure its sources and its tree as ``sources_of`` and ``tree_of`` do."""
    monkeypatch.setattr(run_ci, "sources_digest_of_worktree", sources_of)
    monkeypatch.setattr(run_ci, "worktree_tree", tree_of)


def exits(monkeypatch: pytest.MonkeyPatch) -> StepRuns:
    """Measure in-process and answer ``exit 0`` and ``exit 1`` as the shell would, nothing else."""
    measured_in_process(monkeypatch)
    return install(monkeypatch, {EXIT_0: passes, EXIT_1: ends(ExitStatus(1))})


def ci_runner(
    tmp_path: Path,
    *,
    parallel: bool = False,
    fast: bool = False,
    python: CommandWord = _PYTHON,
    only_lanes: tuple[LaneName, ...] = (),
) -> Runner:
    """Build a Runner writing to a temp log, with all opt-in lanes off.

    Its sources are ``tmp_path``'s, digested by :func:`sources_of`, it names
    no tree, and its build step always runs the staleness gate, so no git is
    asked which files the branch changed.
    """
    ctx = RunContext(
        repo_root=tmp_path,
        branch="test",
        commit="0000000",
        log_path=tmp_path / "ci.log",
        python=python,
        sources=sources_of(tmp_path),
    )
    opts = OptInOptions(
        lanes=OptInLanes(repro=False, stability=False, mutation=False, coverage=False),
        parallel=parallel,
        build_staleness="always",
        fast=fast,
        only_lanes=only_lanes,
    )
    return Runner(opts, ctx)
