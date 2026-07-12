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

from tools._ci_steps import (
    AGDA_GATES_STEP,
    AGDA_SHAKE_TARGETS,
    FAST_STEPS,
    HEAVY_STEPS,
    build_prereq_cmd,
    register_all_steps,
    should_run_staleness,
)
from tools.run_ci import (
    OptInOptions,
    RunContext,
    Runner,
    parse_args,
)

if TYPE_CHECKING:
    from pathlib import Path

    import pytest

# The Agda-gate fan-in folds every cabal-shake gate into one `cabal run shake
# -- <targets>` invocation.  Its hazard is a silently DROPPED gate: a line removed from
# AGDA_SHAKE_TARGETS quietly stops running on every PR.  Guard it by invariants
# rather than a mirror copy of the tuple (DRY) — the count tripwire turns any
# add/drop into a conscious edit, and the named checks pin the load-bearing gates.
_EXPECTED_GATE_COUNT = 14


def test_combined_agda_gates_have_no_silent_drop() -> None:
    """No gate duplicated (which would mask a drop) and the full count is pinned."""
    targets = AGDA_SHAKE_TARGETS
    assert len(set(targets)) == len(targets)  # a dup would hide a drop behind the count
    assert len(targets) == _EXPECTED_GATE_COUNT


def test_combined_agda_gates_include_load_bearing_checks() -> None:
    """The heavy proof checks and the changelog enforcer must be in the fan-in."""
    # check-properties/-fidelity are the heavy proof gates; check-changelog has
    # tripped real PRs — dropping any of them must fail this test, not a PR.
    assert {
        "check-properties",
        "check-fidelity",
        "check-changelog",
        "check-proof-coverage",
    } <= set(AGDA_SHAKE_TARGETS)


def test_combined_agda_step_is_oom_gated() -> None:
    """The combined step carries the heavy proof checks, so it must be OOM-gated."""
    assert AGDA_GATES_STEP in HEAVY_STEPS


def test_build_prereq_runs_the_staleness_gate() -> None:
    """`build_prereq_cmd` returns the staleness-gate command (check_build_incremental).

    This is the `build` step's command when the staleness gate is scheduled (a
    build-graph change, or --build-staleness=always).  Pin it so a refactor can't
    silently swap in a bare `cabal build` that skips the edit/revert→.so
    verification — the failure the old `rm -rf` sledgehammer masked.
    """
    cmd = build_prereq_cmd("python3")
    assert cmd == ["python3", "-m", "tools.check_build_incremental"]


def test_should_run_staleness_decision() -> None:
    """always/never are unconditional; auto follows the build-graph-changed flag."""
    assert should_run_staleness("always", build_graph_changed=False) is True
    assert should_run_staleness("always", build_graph_changed=True) is True
    assert should_run_staleness("never", build_graph_changed=True) is False
    assert should_run_staleness("never", build_graph_changed=False) is False
    assert should_run_staleness("auto", build_graph_changed=True) is True
    assert should_run_staleness("auto", build_graph_changed=False) is False


def test_build_staleness_flag_resolves() -> None:
    """--build-staleness resolves CLI value, defaulting to 'auto'."""
    assert parse_args([]).build_staleness == "auto"
    assert parse_args(["--build-staleness", "always"]).build_staleness == "always"
    assert parse_args(["--build-staleness", "never"]).build_staleness == "never"


def test_build_staleness_env_fallback(monkeypatch: pytest.MonkeyPatch) -> None:
    """Env is honored without a CLI flag; garbage env → 'auto'; CLI overrides env."""
    monkeypatch.setenv("ALETHEIA_BUILD_STALENESS", "always")
    assert parse_args([]).build_staleness == "always"
    monkeypatch.setenv("ALETHEIA_BUILD_STALENESS", "garbage")
    assert parse_args([]).build_staleness == "auto"
    monkeypatch.setenv("ALETHEIA_BUILD_STALENESS", "always")
    assert parse_args(["--build-staleness", "never"]).build_staleness == "never"


def test_heavy_limit_invalid_env_falls_back(monkeypatch: pytest.MonkeyPatch) -> None:
    """A non-integer ALETHEIA_CI_HEAVY_LIMIT must not crash the sweep."""
    monkeypatch.setenv("ALETHEIA_CI_HEAVY_LIMIT", "not-a-number")
    assert parse_args([]).heavy_limit == 2  # the default, not a ValueError


def test_heavy_limit_non_positive_clamped_to_one(monkeypatch: pytest.MonkeyPatch) -> None:
    """0 / negative clamps to 1 so the banner and the scheduler semaphore agree."""
    monkeypatch.setenv("ALETHEIA_CI_HEAVY_LIMIT", "0")
    assert parse_args([]).heavy_limit == 1
    assert parse_args(["--ci-heavy-limit", "-3"]).heavy_limit == 1


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


def test_register_all_steps_populates_the_catalog(tmp_path: Path) -> None:
    """register_all_steps fills the runner with the load-bearing steps, no dups.

    The registration path (``main`` → ``register_all_steps``) is otherwise only
    exercised at real push time, so a moved helper referencing a name that no
    longer resolves after the run_ci/_ci_steps split would import clean, pass
    ``--help``, and only fail on push.  Pin it here.
    """
    runner = _runner(tmp_path)
    register_all_steps(runner, ["cabal", "run", "shake", "--"], runner.opts)
    names = runner.registered_step_names
    # The build prereq, the Agda fan-in, and one step from each binding/lint lane.
    # AGDA_GATES_STEP (not the "agda gates" literal) so a label change can't go stale.
    assert {"build", AGDA_GATES_STEP, "pytest", "ruff", "ubsan ctest"} <= set(names)
    assert len(names) == len(set(names))  # a duplicate name would mask a dropped step


def test_fast_steps_all_resolve_to_registered_steps(tmp_path: Path) -> None:
    """Every FAST_STEPS name resolves to a real registered step (no rename drift).

    ``run_ci --fast`` filters the registry to FAST_STEPS; a name that no longer
    resolves after a step rename (e.g. the gofmt/cargo-fmt split) would silently
    drop that gate from the pre-commit hook.  ``main`` fails loud on this, but
    that path only runs at commit time — pin the invariant here.
    """
    runner = _runner(tmp_path)
    register_all_steps(runner, ["cabal", "run", "shake", "--"], runner.opts)
    registered = set(runner.registered_step_names)
    missing = FAST_STEPS - registered
    assert not missing, f"FAST_STEPS names not in the registry: {sorted(missing)}"


def test_fast_steps_are_never_heavy() -> None:
    """No FAST tier step may be a HEAVY (compile / build-artifact) step.

    The whole point of the split (gofmt vs go vet, cargo fmt vs clippy) is that
    the pre-commit tier is compile-free and needs no build artifacts.  A FAST
    step that is also HEAVY would recompile under the pre-commit stash and/or
    run against a stale ``.so``.
    """
    assert not (FAST_STEPS & HEAVY_STEPS), sorted(FAST_STEPS & HEAVY_STEPS)


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
