# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
"""Orchestrator e2e tests for ``tools.run_ci.Runner`` — the gate guarding the gate.

A failing step MUST make ``run()`` return 1 (never a silent green), a ``build``
failure MUST short-circuit the sweep, and serial and parallel modes must agree
on pass/fail.  Synthetic exit-code steps only — no real gates, no timing asserts.
This is the [[feedback_orchestrator_end_to_end_validation]] check at the run()
level (the lane scheduler itself is covered by test_scheduler.py).
"""

from __future__ import annotations

from typing import TYPE_CHECKING

from tools.run_ci import OptInOptions, RunContext, Runner

if TYPE_CHECKING:
    from pathlib import Path


def _runner(tmp_path: Path, *, parallel: bool = False) -> Runner:
    """Build a Runner writing to a temp log, with all opt-in lanes off."""
    ctx = RunContext(
        repo_root=tmp_path,
        branch="test",
        commit="0000000",
        log_path=tmp_path / "ci.log",
        python="python3",
    )
    opts = OptInOptions(repro=False, stability=False, mutation=False, parallel=parallel)
    return Runner(opts, ctx)


def test_all_pass_returns_zero(tmp_path: Path) -> None:
    """Every step passing ⇒ exit code 0."""
    runner = _runner(tmp_path)
    runner.step("a", "exit 0", lane="x")
    runner.step("b", "exit 0", lane="y")
    assert runner.run() == 0


def test_failure_returns_one(tmp_path: Path) -> None:
    """A single failing step ⇒ exit code 1 (no silent green)."""
    runner = _runner(tmp_path)
    runner.step("ok", "exit 0", lane="x")
    runner.step("bad", "exit 1", lane="y")
    assert runner.run() == 1


def test_build_failure_short_circuits(tmp_path: Path) -> None:
    """A failing ``build`` aborts the sweep before any lane runs."""
    runner = _runner(tmp_path)
    runner.step("build", "exit 1", lane="agda")
    runner.step("after", "echo SHOULD_NOT_RUN; exit 0", lane="x")
    assert runner.run() == 1
    log = (tmp_path / "ci.log").read_text(encoding="utf-8")
    assert "SHOULD_NOT_RUN" not in log  # the post-build step never executed


def test_parallel_mode_passes(tmp_path: Path) -> None:
    """Parallel mode returns 0 when every lane passes."""
    runner = _runner(tmp_path, parallel=True)
    runner.step("a", "exit 0", lane="x")
    runner.step("b", "exit 0", lane="y")
    assert runner.run() == 0


def test_parallel_mode_surfaces_failure(tmp_path: Path) -> None:
    """Parallel mode still returns 1 when any lane fails."""
    runner = _runner(tmp_path, parallel=True)
    runner.step("a", "exit 0", lane="x")
    runner.step("boom", "exit 5", lane="y")
    assert runner.run() == 1
