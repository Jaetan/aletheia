# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
"""Orchestrator e2e tests for ``tools.run_ci.Runner`` — the gate guarding the gate.

A failing step MUST make ``run()`` return 1 (never a silent green), a ``build``
failure MUST short-circuit the sweep, and serial and parallel modes must agree
on pass/fail.  Synthetic exit-code steps only — no real gates, no timing asserts.
This is the orchestrator end-to-end validation check at the run()
level (the lane scheduler itself is covered by test_scheduler.py).
"""

from __future__ import annotations

import os
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
from tools._common import find_executable, run_capture
from tools.check_gate_claim import (
    SOURCES_ENV,
    SOURCES_LINE,
    SOURCES_UNRECORDED,
    evidence_for,
    sources_digest_of_worktree,
)
from tools.run_ci import (
    OptInLanes,
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


def _runner(tmp_path: Path, *, parallel: bool = False, fast: bool = False) -> Runner:
    """Build a Runner writing to a temp log, with all opt-in lanes off.

    ``tmp_path`` becomes a git repository, since the sweep digests the build
    sources it observes at the start and re-measures them at the end.
    """
    init = run_capture([find_executable("git"), "-C", str(tmp_path), "init", "-q"])
    assert init.returncode == 0, init.stderr
    ctx = RunContext(
        repo_root=tmp_path,
        branch="test",
        commit="0000000",
        log_path=tmp_path / "ci.log",
        python="python3",
        sources=sources_digest_of_worktree(tmp_path),
    )
    opts = OptInOptions(
        lanes=OptInLanes(repro=False, stability=False, mutation=False),
        parallel=parallel,
        fast=fast,
    )
    return Runner(opts, ctx)


def _build_dir(cmd: str) -> str:
    """Return the ``cmake -B`` directory a shell step configures."""
    marker = "cmake -B "
    start = cmd.index(marker) + len(marker)
    return cmd[start:].split(" ", 1)[0]


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
    assert {"build", AGDA_GATES_STEP, "pytest", "ruff", "ubsan ctest", "asan ctest"} <= set(names)
    assert len(names) == len(set(names))  # a duplicate name would mask a dropped step


def test_each_sanitizer_lane_owns_its_tree_and_its_lane(tmp_path: Path) -> None:
    """The two sanitizer ctest steps share neither a build tree nor a lane.

    Sanitizer flags are not safe to mix in one archive, and two steps in one
    lane run in turn rather than beside each other.  A copy-edited step that
    kept the other's ``-B`` directory would build one tree twice, each time
    with the other's flags, and read as a passing lane.
    """
    runner = _runner(tmp_path)
    register_all_steps(runner, ["cabal", "run", "shake", "--"], runner.opts)
    lanes = {
        step.name: step
        for step in runner.registered_steps
        if step.name in {"ubsan ctest", "asan ctest"}
    }
    assert set(lanes) == {"ubsan ctest", "asan ctest"}
    assert {step.lane for step in lanes.values()} == {"ubsan", "asan"}
    trees = {name: _build_dir(str(step.cmd)) for name, step in lanes.items()}
    assert trees == {"ubsan ctest": "build-ubsan", "asan ctest": "build-asan"}
    for name, step in lanes.items():
        assert f"--test-dir {trees[name]}" in str(step.cmd)
        assert step.heavy, f"{name} builds a whole tree and is heavy"


def test_each_sanitizer_lane_reads_its_tree_back_before_building(tmp_path: Path) -> None:
    """Each sanitizer step asserts the configured tree carries the sanitizer it asked for.

    CMake drops a cache whose compiler has changed and configures afresh, and a
    tree that comes back without ``ALETHEIA_SANITIZER`` builds uninstrumented,
    runs the battery green and reports as a sanitizer lane.  The lane reads the
    value back from the cache, so that tree fails where it is built.
    """
    runner = _runner(tmp_path)
    register_all_steps(runner, ["cabal", "run", "shake", "--"], runner.opts)
    wanted = {"ubsan ctest": "undefined", "asan ctest": "address"}
    for name, sanitizer in wanted.items():
        step = next(entry for entry in runner.registered_steps if entry.name == name)
        cmd = str(step.cmd)
        tree = _build_dir(cmd)
        assert f"grep -qx 'ALETHEIA_SANITIZER:STRING={sanitizer}' {tree}/CMakeCache.txt" in cmd
        assert cmd.index("CMakeCache.txt") < cmd.index("cmake --build"), (
            f"{name} reads the cache back before it builds"
        )


def test_the_asan_lane_asks_for_stack_use_after_return(tmp_path: Path) -> None:
    """The ASan step names the option rather than relying on the runtime default.

    Stack-use-after-return detection is the one class this lane reads that no
    other always-on gate does, and whether it is on by default is the sanitizer
    runtime's business, not this repository's.  A step that dropped the option
    would still pass and would still be called a sanitizer lane.
    """
    runner = _runner(tmp_path)
    register_all_steps(runner, ["cabal", "run", "shake", "--"], runner.opts)
    step = next(entry for entry in runner.registered_steps if entry.name == "asan ctest")
    assert "ASAN_OPTIONS=detect_stack_use_after_return=1" in str(step.cmd)
    assert "-DALETHEIA_SANITIZER=address" in str(step.cmd)


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


def test_live_progress_streams_to_stderr(
    tmp_path: Path, capsys: pytest.CaptureFixture[str]
) -> None:
    """Each step draws a live start line and a live outcome line on stderr.

    The log keeps its deterministic ✓/✗ record; the terminal channel is the
    live one — this pins that the runner emits both halves.
    """
    runner = _runner(tmp_path)
    runner.step("quickstep", "exit 0", lane="x")
    assert runner.run() == 0
    err = capsys.readouterr().err
    assert "▶ quickstep" in err
    assert "✓ quickstep" in err
    log = (tmp_path / "ci.log").read_text(encoding="utf-8")
    assert "✓ quickstep" in log  # the deterministic record still lands in the log
    # Dense blocks: the header rule is the separator; an empty-output step's
    # ✓ line follows its header directly — no filler blank lines in the log.
    assert "quickstep (0s) ───\n  ✓ quickstep" in log
    assert "\n\n─── quickstep" not in log


def test_a_full_sweep_records_and_exports_the_sources_it_observes(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    """The header carries the digest, every step sees it, and the export is undone.

    The gate-claim enforcer runs inside the sweep, before any log of it is
    finished, so the export is the only way it can learn which tree the sweep
    observes; the header is what it reads once the log is finished.
    """
    monkeypatch.delenv(SOURCES_ENV, raising=False)
    runner = _runner(tmp_path)
    runner.step("observe", f"echo seen=${SOURCES_ENV}", lane="x")
    assert runner.run() == 0
    log = (tmp_path / "ci.log").read_text(encoding="utf-8")
    assert f"{SOURCES_LINE}{runner.ctx.sources}\n" in log
    assert f"seen={runner.ctx.sources}" in log
    assert SOURCES_ENV not in os.environ


def test_a_full_sweep_that_passed_is_read_back_as_evidence(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    """The log a passing sweep leaves is one the enforcer accepts for its digest.

    The writer and the reader are pinned to each other here: a summary line
    reworded on one side without the other is a sweep whose evidence nothing
    can read.
    """
    monkeypatch.delenv(SOURCES_ENV, raising=False)
    runner = _runner(tmp_path)
    runner.step("a", "exit 0", lane="x")
    assert runner.run() == 0
    assert evidence_for(runner.ctx.sources, log_dir=tmp_path, environ={}) is not None
    assert evidence_for("0" * 64, log_dir=tmp_path, environ={}) is None


def test_a_fast_sweep_records_no_sources_and_exports_none(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    """A fast-tier sweep runs a subset, so its passing log vouches for no tree."""
    monkeypatch.setenv(SOURCES_ENV, "stale-from-a-caller")
    runner = _runner(tmp_path, fast=True)
    runner.step("observe", f"echo seen=[${SOURCES_ENV}]", lane="x")
    assert runner.run() == 0
    log = (tmp_path / "ci.log").read_text(encoding="utf-8")
    assert f"{SOURCES_LINE}{SOURCES_UNRECORDED}\n" in log
    assert "seen=[]" in log
    assert os.environ[SOURCES_ENV] == "stale-from-a-caller"
    assert evidence_for(runner.ctx.sources, log_dir=tmp_path, environ={}) is None


def test_a_sweep_whose_sources_moved_under_it_fails(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    """Every step passed, but a build source changed meanwhile: no record, exit 1."""
    monkeypatch.delenv(SOURCES_ENV, raising=False)
    runner = _runner(tmp_path)
    runner.step(
        "edit", "mkdir -p src && echo 'module A where' > src/A.agda", cwd=tmp_path, lane="x"
    )
    assert runner.run() == 1
    log = (tmp_path / "ci.log").read_text(encoding="utf-8")
    assert "build sources moved during the sweep" in log
    assert evidence_for(runner.ctx.sources, log_dir=tmp_path, environ={}) is None
