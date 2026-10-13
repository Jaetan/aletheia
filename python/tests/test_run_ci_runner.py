# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
"""Orchestrator e2e tests for ``tools.run_ci.Runner`` — the gate guarding the gate.

A failing step MUST make ``run()`` return 1 (never a silent green), a ``build``
failure MUST short-circuit the sweep, and serial and parallel modes must agree
on pass/fail.  Each step's command is answered in-process by a stand-in
(``_step_runs``), and the sweep's measures of its build sources and its tree
are taken from the planted files without git: no real gates, no timing
asserts.  This is the orchestrator end-to-end validation check at the run()
level (the lane scheduler itself is covered by test_scheduler.py).
"""

from __future__ import annotations

import os
import shlex
import subprocess
import sys
import tomllib
from dataclasses import replace
from pathlib import Path, PurePosixPath

import pytest
from _ci_runner import EXIT_0, ci_runner, exits
from _processes import CommandWord

from tools import _ci_steps
from tools._ci_steps import (
    AGDA_GATES_STEP,
    AGDA_SHAKE_TARGETS,
    CPP_COMPILERS,
    CPP_LINT_LANE,
    DOC_EXAMPLE_DOCS,
    FAST_STEPS,
    HEAVY_STEPS,
    ROOT_PYTHON,
    build_graph_touched,
    build_prereq_cmd,
    in_every_go_module,
    register_all_steps,
    should_run_staleness,
)
from tools._common import (
    CPP_LINT_TREE,
    RelPath,
    find_executable,
    git_ls_files,
    run_capture,
)
from tools._resources import cpu_budget
from tools.run_ci import (
    LaneName,
    Runner,
    parse_args,
)

from aletheia.common_types import ExitStatus, Prose

# The Agda-gate fan-in folds every cabal-shake gate into one `cabal run shake
# -- <targets>` invocation.  Its hazard is a silently DROPPED gate: a line removed from
# AGDA_SHAKE_TARGETS quietly stops running on every PR.  Guard it by invariants
# rather than a mirror copy of the tuple (DRY) — the count tripwire turns any
# add/drop into a conscious edit, and the named checks pin the load-bearing gates.
_EXPECTED_GATE_COUNT = 15

# The status of a command that succeeded.
_SUCCEEDED = ExitStatus(0)


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


def _diff_naming(
    monkeypatch: pytest.MonkeyPatch, changed: RelPath, *, status: ExitStatus = _SUCCEEDED
) -> list[list[CommandWord]]:
    """Answer the build-graph question's ``git diff`` with ``changed``; return what was asked."""
    asked: list[list[CommandWord]] = []

    def answer_the_diff(cmd: list[CommandWord]) -> subprocess.CompletedProcess[Prose]:
        asked.append(cmd)
        return subprocess.CompletedProcess(cmd, status, Prose(f"{changed}\n"), Prose(""))

    monkeypatch.setattr(_ci_steps, "run_capture", answer_the_diff)
    return asked


def _diff_against_main(repo: Path) -> list[CommandWord]:
    """Return the argv the build-graph question runs: the branch's changes since ``main``."""
    git = find_executable("git")
    return [CommandWord(w) for w in (git, "-C", str(repo), "diff", "--name-only", "main...HEAD")]


@pytest.mark.parametrize(
    "changed",
    [
        RelPath("Shakefile.hs"),
        RelPath("shake/Rules/Library.hs"),
        RelPath("haskell-shim/src/AletheiaFFI.hs"),
    ],
)
def test_a_branch_touching_the_build_graph_is_seen(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch, changed: RelPath
) -> None:
    """A branch changing the build program or the shim changed the graph the gate checks."""
    asked = _diff_naming(monkeypatch, changed)
    assert build_graph_touched(tmp_path)
    assert asked == [_diff_against_main(tmp_path)]


def test_a_branch_touching_a_document_leaves_the_graph(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    """A branch changing a document only leaves the build graph as it was."""
    asked = _diff_naming(monkeypatch, RelPath("docs/BUILDING.md"))
    assert not build_graph_touched(tmp_path)
    assert asked == [_diff_against_main(tmp_path)]


def test_a_diff_git_cannot_give_counts_as_a_touched_graph(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    """With no diff to read, the staleness gate runs rather than being skipped unseen."""
    _ = _diff_naming(monkeypatch, RelPath("docs/BUILDING.md"), status=ExitStatus(128))
    assert build_graph_touched(tmp_path)


@pytest.mark.parametrize(
    ("changed", "staleness"),
    [(RelPath("shake/Rules/Library.hs"), True), (RelPath("docs/BUILDING.md"), False)],
)
def test_under_auto_the_build_step_is_the_staleness_gate_when_the_graph_changed(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch, changed: RelPath, *, staleness: bool
) -> None:
    """``auto`` asks git what the branch changed, and builds plainly unless the graph moved."""
    asked = _diff_naming(monkeypatch, changed)
    runner = ci_runner(tmp_path)
    runner = Runner(replace(runner.opts, build_staleness="auto"), runner.ctx)
    cabal = ["cabal", "run", "shake", "--"]
    register_all_steps(runner, cabal, runner.opts)
    (build,) = (step for step in runner.registered_steps if step.name == "build")
    assert build.cmd == (build_prereq_cmd(runner.python) if staleness else [*cabal, "build"])
    assert asked == [_diff_against_main(tmp_path)]


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
    runner = ci_runner(tmp_path)
    register_all_steps(runner, ["cabal", "run", "shake", "--"], runner.opts)
    names = runner.registered_step_names
    # The build prereq, the Agda fan-in, and one step from each binding/lint lane.
    # AGDA_GATES_STEP (not the "agda gates" literal) so a label change can't go stale.
    assert {"build", AGDA_GATES_STEP, "pytest", "ruff", "ubsan ctest", "asan ctest"} <= set(names)
    assert len(names) == len(set(names))  # a duplicate name would mask a dropped step


@pytest.mark.process("which Python files the repository tracks is git's own answer")
def test_every_tracked_python_file_is_read_by_all_three_linters(tmp_path: Path) -> None:
    """ruff, basedpyright and pylint each read every tracked Python file.

    ``.archive/`` aside: ruff reads ``python/`` whole and the other two its
    ``aletheia/``, ``tests/`` and ``benchmarks/``, and all three read every
    entry of ``ROOT_PYTHON``.  A file none of those covers is linted by none of
    the three, and one linter reading less than its peers is the asymmetry the
    shared list exists to prevent.
    """
    runner = ci_runner(tmp_path)
    register_all_steps(runner, ["cabal", "run", "shake", "--"], runner.opts)
    steps = {step.name: step for step in runner.registered_steps}
    ruff_cmd = steps["ruff"].cmd
    assert isinstance(ruff_cmd, str)
    ruff_args = shlex.split(ruff_cmd)
    package = ["aletheia/", "tests/", "benchmarks/"]
    for root in ROOT_PYTHON:
        # check and format --check each name the list once.
        assert ruff_args.count(str(root)) == 2, f"ruff does not read {root}"
    assert ruff_args.count("python") == 2
    for linter in ("basedpyright", "pylint"):
        args = list(steps[linter].cmd)
        missing = [p for p in [*package, *(str(".." / p) for p in ROOT_PYTHON)] if p not in args]
        assert not missing, f"{linter} does not read {missing}"
    repo = Path(__file__).resolve().parents[2]
    under_package = [PurePosixPath("python", p) for p in package]
    under_root = [PurePosixPath(p) for p in ROOT_PYTHON]
    unlinted = [
        rel
        for rel in git_ls_files(repo, "*.py")
        if not rel.startswith(".archive/")
        and not any(PurePosixPath(rel).is_relative_to(d) for d in (*under_package, *under_root))
    ]
    assert not unlinted, f"tracked Python no linter reads: {unlinted}"


def test_basedpyright_leaves_the_kept_outputs_under_tools_unread() -> None:
    """The basedpyright step is told to leave ``tools/ci-output`` alone.

    The step hands basedpyright the directory ``tools`` whole, and basedpyright,
    unlike ruff, does not read the ignore list, so a helper script kept under
    ``tools/ci-output`` (logs and scratch no gate owns) would be type-checked
    with the gates and fail the sweep.  The exclusion is the configuration's,
    read here as the step would read it.
    """
    repo = Path(__file__).resolve().parents[2]
    config = tomllib.loads((repo / "python" / "pyproject.toml").read_text(encoding="utf-8"))
    excluded = config["tool"]["basedpyright"].get("exclude", [])
    assert "../tools/ci-output" in excluded, f"basedpyright reads tools/ci-output: {excluded}"


def test_the_doc_example_step_reads_exactly_the_harness_documents(tmp_path: Path) -> None:
    """The doc-example step's document arguments are ``DOC_EXAMPLE_DOCS``, all of them and last.

    A directory given beside the list, or a document spelled into the step
    rather than into the list, runs fences the structural tests and the
    documented command do not read.
    """
    runner = ci_runner(tmp_path)
    register_all_steps(runner, ["cabal", "run", "shake", "--"], runner.opts)
    steps = {step.name: step for step in runner.registered_steps}
    cmd = list(steps["pytest --markdown-docs"].cmd)
    documents = [str(doc) for doc in DOC_EXAMPLE_DOCS]
    assert cmd[-len(documents) :] == documents
    # The argument before the documents is the last option's value, so nothing
    # else is collected.
    assert cmd[-len(documents) - 1] == "pythonpath=python/tests"


@pytest.mark.process(
    "the mode git's index records for each tracked file, the one CI checks out, is git's answer"
)
def test_a_tracked_python_file_has_a_shebang_exactly_when_git_marks_it_executable() -> None:
    """A tracked Python file outside ``.archive/`` is executable iff it has a shebang.

    ruff's EXE001 and EXE002 hold this in CI, but ruff skips both under WSL,
    where file modes are unreliable, so a local sweep there passes what CI
    fails.  This reads the modes git records, the ones CI checks out.
    """
    repo = Path(__file__).resolve().parents[2]
    listed = run_capture([find_executable("git"), "-C", str(repo), "ls-files", "-s", "--", "*.py"])
    assert listed.returncode == 0, listed.stderr
    mismatched = [
        path
        for meta, path in (line.split("\t", 1) for line in listed.stdout.splitlines())
        if not path.startswith(".archive/")
        and meta.startswith("100755") != (repo / path).read_bytes().startswith(b"#!")
    ]
    assert not mismatched, f"shebang and executable bit disagree: {mismatched}"


def test_each_sanitizer_lane_owns_its_tree_and_its_lane(tmp_path: Path) -> None:
    """The two sanitizer ctest steps share neither a build tree nor a lane.

    Sanitizer flags are not safe to mix in one archive, and two steps in one
    lane run in turn rather than beside each other.  A copy-edited step that
    kept the other's ``-B`` directory would build one tree twice, each time
    with the other's flags, and read as a passing lane.
    """
    runner = ci_runner(tmp_path)
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


def test_the_compile_database_gates_run_beside_the_test_build(tmp_path: Path) -> None:
    """clang-tidy and the checks reading its database share a lane the test build is not in.

    The lane's first step configures the lint tree with the binding's
    compilers and lints from that tree's database, so the checks after it read
    a database that exists; the cpp lane, which builds and runs the tests,
    holds none of them, so none waits for that build.
    """
    runner = ci_runner(tmp_path)
    register_all_steps(runner, ["cabal", "run", "shake", "--"], runner.opts)
    gates = ["clang-tidy", "check-clang-tidy-coverage", "check-cpp-ast", "check-cpp-const-locals"]
    lane = [step for step in runner.registered_steps if step.lane == CPP_LINT_LANE]
    assert [step.name for step in lane] == gates
    tidy = str(lane[0].cmd)
    assert _build_dir(tidy) == CPP_LINT_TREE
    assert CPP_COMPILERS in tidy
    assert f" -p {CPP_LINT_TREE} cpp/src/ cpp/tests/ cpp/benchmarks/" in tidy
    cpp = [step.name for step in runner.registered_steps if step.lane == "cpp"]
    assert "ctest" in cpp
    assert not set(gates) & set(cpp)


def test_clang_tidy_is_told_the_step_budget(tmp_path: Path) -> None:
    """run-clang-tidy runs with the job count every gate step takes, never its own.

    Left to itself it starts one job per CPU of the machine, whatever CPUs the
    sweep was given, beside the other lanes.
    """
    runner = ci_runner(tmp_path)
    register_all_steps(runner, ["cabal", "run", "shake", "--"], runner.opts)
    (tidy,) = [step for step in runner.registered_steps if step.name == "clang-tidy"]
    assert f"run-clang-tidy-23 -j {cpu_budget()} -quiet " in str(tidy.cmd)


def test_the_const_locals_gate_is_told_the_step_budget(tmp_path: Path) -> None:
    """The const-locals gate compiles with the job count every gate step takes."""
    runner = ci_runner(tmp_path)
    register_all_steps(runner, ["cabal", "run", "shake", "--"], runner.opts)
    (gate,) = [step for step in runner.registered_steps if step.name == "check-cpp-const-locals"]
    assert list(gate.cmd)[-2:] == ["--jobs", str(cpu_budget())]


def test_the_full_ci_parts_split_every_lane_between_them(tmp_path: Path) -> None:
    """Each lane the sweep registers runs in exactly one part of the full-CI job.

    A lane no part names would run nowhere on a pull request, and one two
    parts name would run twice.  The parts' lists are read from the workflow;
    the runner here registers what the job does, with no opt-in lane.
    """
    runner = ci_runner(tmp_path)
    register_all_steps(runner, ["cabal", "run", "shake", "--"], runner.opts)
    registered = sorted({step.lane for step in runner.registered_steps})
    workflow = Path(__file__).resolve().parents[2] / ".github" / "workflows" / "pr-full-ci.yml"
    named = [
        lane.strip()
        for line in workflow.read_text(encoding="utf-8").splitlines()
        if line.strip().startswith("lanes: ")
        for lane in line.strip().removeprefix("lanes: ").split(",")
    ]
    assert sorted(named) == registered


def test_full_ci_caches_the_dependencies_of_every_tree_it_configures(tmp_path: Path) -> None:
    """The full-CI job caches FetchContent's downloads for exactly the trees the sweep configures.

    A tree the cache leaves out downloads every dependency on every run, and a
    path naming a tree no step configures caches nothing.  The job runs the
    sweep with no opt-in lane, as the runner here is built.
    """
    runner = ci_runner(tmp_path)
    register_all_steps(runner, ["cabal", "run", "shake", "--"], runner.opts)
    commands = [str(step.cmd) for step in runner.registered_steps]
    trees = {_build_dir(command) for command in commands if "cmake -B " in command}
    workflow = Path(__file__).resolve().parents[2] / ".github" / "workflows" / "pr-full-ci.yml"
    lines = workflow.read_text(encoding="utf-8").splitlines()
    start = lines.index("      - name: Cache C++ FetchContent deps")
    end = next(i for i in range(start + 1, len(lines)) if lines[i].lstrip().startswith("key:"))
    cached = {line.strip() for line in lines[start:end] if line.strip().endswith("/_deps")}
    assert cached == {f"cpp/{tree}/_deps" for tree in trees}


def test_each_sanitizer_lane_reads_its_tree_back_before_building(tmp_path: Path) -> None:
    """Each sanitizer step asserts the configured tree carries the sanitizer it asked for.

    CMake drops a cache whose compiler has changed and configures afresh, and a
    tree that comes back without ``ALETHEIA_SANITIZER`` builds uninstrumented,
    runs the battery green and reports as a sanitizer lane.  The lane reads the
    value back from the cache, so that tree fails where it is built.
    """
    runner = ci_runner(tmp_path)
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
    runner = ci_runner(tmp_path)
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
    runner = ci_runner(tmp_path)
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


def test_live_progress_streams_to_stderr(
    tmp_path: Path, capsys: pytest.CaptureFixture[str], monkeypatch: pytest.MonkeyPatch
) -> None:
    """Each step draws a live start line and a live outcome line on stderr.

    The log keeps its deterministic ✓/✗ record; the terminal channel is the
    live one — this pins that the runner emits both halves.
    """
    _ = exits(monkeypatch)
    runner = ci_runner(tmp_path)
    runner.step("quickstep", EXIT_0, lane="x")
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


def test_lanes_parse_into_the_names_given() -> None:
    """The option takes lane names separated by commas, spaces around them dropped."""
    assert parse_args(["--lanes", "cpp, ubsan,asan"]).only_lanes == ("cpp", "ubsan", "asan")
    assert not parse_args([]).only_lanes


def test_an_empty_lane_name_is_refused() -> None:
    """A doubled comma would otherwise name a lane nothing registers into, silently."""
    with pytest.raises(SystemExit):
        _ = parse_args(["--lanes", "cpp,,asan"])


def _three_lanes(runner: Runner) -> None:
    """Register a build and steps in two lanes, interleaved."""
    runner.step("build", "exit 0", lane="agda")
    runner.step("a1", "exit 0", lane="a")
    runner.step("b1", "exit 0", lane="b")
    runner.step("a2", "exit 0", lane="a")


def test_a_lane_subset_keeps_the_build_and_those_lanes_alone(tmp_path: Path) -> None:
    """The build prereq every lane needs stays; another lane's steps go."""
    runner = ci_runner(tmp_path)
    _three_lanes(runner)
    assert runner.restrict_to_lanes((LaneName("a"),)) is None
    assert runner.registered_step_names == ("build", "a1", "a2")


def test_a_lane_no_step_registers_into_is_refused(tmp_path: Path) -> None:
    """A misspelt lane is refused and the registry left whole, not a smaller sweep run."""
    runner = ci_runner(tmp_path)
    _three_lanes(runner)
    refusal = runner.restrict_to_lanes((LaneName("a"), LaneName("nope")))
    assert refusal is not None
    assert "nope" in refusal
    assert runner.registered_step_names == ("build", "a1", "b1", "a2")


def test_lanes_beside_the_fast_tier_are_refused(tmp_path: Path) -> None:
    """Two subsets at once would leave which gates ran to the order they were applied in."""
    runner = ci_runner(tmp_path, fast=True)
    _three_lanes(runner)
    refusal = runner.restrict_to_lanes((LaneName("a"),))
    assert refusal is not None
    assert "--fast" in refusal


def _one_message_tree(root: Path, python_dir: Path) -> None:
    """Lay out every path the pylint step reads: 2100 clean statements, one missing docstring.

    The package's three directories hold the statements, each entry of
    ``ROOT_PYTHON`` a clean module of its own, and ``tools/`` the one message.
    """
    for package in ("aletheia", "tests", "benchmarks"):
        clean = "".join(f"{package.upper()}_{n} = {n}\n" for n in range(700))
        (python_dir / package).mkdir(parents=True)
        _ = (python_dir / package / "constants.py").write_text(
            '"""Constants."""\n' + clean, encoding="utf-8"
        )
    for entry in ROOT_PYTHON:
        module = root / entry if entry.suffix == ".py" else root / entry / f"{entry.name}_clean.py"
        module.parent.mkdir(parents=True, exist_ok=True)
        _ = module.write_text('"""Clean."""\n', encoding="utf-8")
    _ = (root / "tools" / "undocumented.py").write_text("VALUE = 1\n", encoding="utf-8")


def _scratch_pylint_home(root: Path) -> dict[str, str]:
    """Return the environment with pylint's stored scores kept under ``root``."""
    return os.environ | {"PYLINTHOME": str(root / "pylint-home")}


_THE_LINTER_ANSWERS = (
    "the exit status and score are the linter's own answer under the given argv and config"
)


@pytest.mark.process(_THE_LINTER_ANSWERS)
def test_pylint_step_fails_on_a_message_the_score_rounds_away(tmp_path: Path) -> None:
    """The pylint step fails on one message even where the score reads 10.00.

    pylint's score rounds a few messages over the tree's statement count to
    10.00, so a step that read the score passed a tree carrying messages.  The
    scratch tree holds 2100 clean statements and one module without a
    docstring: the score still prints 10.00, and the step has to fail.
    """
    # pylint looks for its configuration upward from the step's directory and
    # stops at a directory holding ``.git``: the scratch tree's own.
    (tmp_path / ".git").mkdir()
    runner = ci_runner(tmp_path, python=CommandWord(sys.executable))
    register_all_steps(runner, ["cabal", "run", "shake", "--"], runner.opts)
    (step,) = (entry for entry in runner.registered_steps if entry.name == "pylint")
    assert step.cwd is not None
    _one_message_tree(tmp_path, step.cwd)
    argv = ["/bin/sh", "-c", step.cmd] if isinstance(step.cmd, str) else list(step.cmd)
    result = run_capture(argv, cwd=step.cwd, env=_scratch_pylint_home(tmp_path))
    assert "rated at 10.00/10" in result.stdout, result.stdout
    assert result.returncode != 0, result.stdout


@pytest.mark.process(_THE_LINTER_ANSWERS)
def test_pylint_config_fails_any_message_and_scores_it(tmp_path: Path) -> None:
    """Under the repository's pylint config one message fails the run and costs a point.

    ``fail-on`` makes the exit status non-zero on any message even with the
    score threshold lowered to 0, and ``evaluation`` scores per message rather
    than per statement, so the scratch tree the default formula rates 10.00
    reads 9.00.
    """
    python_dir = tmp_path / "python"
    _one_message_tree(tmp_path, python_dir)
    rcfile = Path(__file__).resolve().parent.parent / "pyproject.toml"
    argv = [sys.executable, "-m", "pylint", f"--rcfile={rcfile}", "--fail-under=0"]
    argv += ["aletheia/", "tests/", "benchmarks/", "../tools/"]
    result = run_capture(argv, cwd=python_dir, env=_scratch_pylint_home(tmp_path))
    assert "rated at 9.00/10" in result.stdout, result.stdout
    assert result.returncode != 0, result.stdout


_A_SHELL_RUNS_THE_LOOP = (
    "only a POSIX shell answers how it runs the loop's && and || chains, test -n and subshell cd"
)


def _go_loop(tmp_path: Path, listing: list[str], cmd: str, *, list_status: int = 0) -> int:
    """Run :func:`in_every_go_module` over ``cmd`` with a ``go`` that lists ``listing``."""
    bin_dir = tmp_path / "bin"
    bin_dir.mkdir()
    go = bin_dir / "go"
    lines = "".join(f"{entry}\n" for entry in listing)
    _ = go.write_text(f"#!/bin/sh\nprintf '%s' '{lines}'\nexit {list_status}\n", encoding="utf-8")
    go.chmod(0o755)
    sh = find_executable("sh")
    env = os.environ | {"PATH": f"{bin_dir}{os.pathsep}{os.environ['PATH']}"}
    return run_capture([sh, "-c", in_every_go_module(cmd)], cwd=tmp_path, env=env).returncode


@pytest.mark.process(_A_SHELL_RUNS_THE_LOOP)
def test_the_go_module_loop_runs_the_command_in_every_listed_module(tmp_path: Path) -> None:
    """Every module ``go list -m`` names gets the command, and the step passes."""
    modules = [tmp_path / name for name in ("core", "cli", "excel")]
    for module in modules:
        module.mkdir()
    assert _go_loop(tmp_path, [str(m) for m in modules], "touch ran") == 0
    assert all((m / "ran").exists() for m in modules)


@pytest.mark.process(_A_SHELL_RUNS_THE_LOOP)
def test_the_go_module_loop_fails_when_one_module_fails(tmp_path: Path) -> None:
    """A module whose command fails fails the step, wherever it sits in the list."""
    modules = [tmp_path / name for name in ("core", "cli", "excel")]
    for module in modules:
        module.mkdir()
    listing = [str(m) for m in modules]
    assert _go_loop(tmp_path, listing, 'test "$(basename "$PWD")" != cli') == 1


@pytest.mark.process(_A_SHELL_RUNS_THE_LOOP)
def test_the_go_module_loop_fails_when_the_listing_fails_or_is_empty(tmp_path: Path) -> None:
    """A workspace go cannot list, or one listing nothing, is a failure, never a pass."""
    (tmp_path / "failed").mkdir()
    (tmp_path / "empty").mkdir()
    assert _go_loop(tmp_path / "failed", [], "true", list_status=1) == 1
    assert _go_loop(tmp_path / "empty", [], "true") == 1
