# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
"""Every GitHub Actions step runs under the watchdog, declared watched or exempt.

Every ``run:`` step of every workflow is declared in ``tools/_workflow_steps.py``:
watched when it runs our tooling, exempt when only GitHub runs it.  Every job
that checks out the tree runs its steps under ``tools.watch_step``, the shell
its workflow names, having checked out the tree and set up Python 3.14 before
its first ``run:`` step; a job that checks out nothing has no tooling to run,
so it runs GitHub's own default shell and only exempt steps.  A script running
our tooling is watched however many setup lines it also has; one running two
watched tools, or none and nothing exempt, is refused.
"""

from __future__ import annotations

from pathlib import Path
from typing import TYPE_CHECKING, NewType, TypedDict, cast

import pytest
import yaml

from tools._ci_progress import ALLOWANCE_FLOOR, STEP_PROGRESS
from tools._watchdog import Chunk, heard_line
from tools._workflow_steps import WATCHED, ScriptText, WorkflowStep, declared_for

if TYPE_CHECKING:
    from collections.abc import Iterator

    from tools._watchdog import Line

    from aletheia.common_types import Prose

_WORKFLOWS = Path(__file__).resolve().parents[2] / ".github" / "workflows"

# A shell line as a workflow names it; an action a step uses; a step's name; a job's id; a
# Python version as setup-python reads it; a place in the workflows, file and job.
ShellLine = NewType("ShellLine", str)
ActionRef = NewType("ActionRef", str)
StepName = NewType("StepName", str)
JobId = NewType("JobId", str)
PythonVersion = NewType("PythonVersion", str)
Place = NewType("Place", str)

# The shell every job that checks out the tree names, and GitHub's own default.
_WATCHED_SHELL = ShellLine("python3.14 -m tools.watch_step {0}")
_GITHUB_SHELL = ShellLine("bash -e {0}")

_With = TypedDict("_With", {"python-version": PythonVersion}, total=False)
_Step = TypedDict(
    "_Step",
    {
        "name": StepName,
        "run": ScriptText,
        "uses": ActionRef,
        "with": _With,
        "shell": ShellLine,
        "working-directory": Place,
    },
    total=False,
)


class _RunDefaults(TypedDict, total=False):
    shell: ShellLine


class _Defaults(TypedDict, total=False):
    run: _RunDefaults


class _Job(TypedDict, total=False):
    steps: list[_Step]
    defaults: _Defaults
    container: Place


class _Workflow(TypedDict, total=False):
    jobs: dict[JobId, _Job]
    defaults: _Defaults


def _jobs() -> Iterator[tuple[Place, _Job, _Workflow]]:
    """Each job of each workflow, with its place and its workflow."""
    for path in sorted(_WORKFLOWS.glob("*.yml")):
        workflow = cast("_Workflow", yaml.safe_load(path.read_text(encoding="utf-8")))
        for job_id, job in workflow.get("jobs", {}).items():
            yield Place(f"{path.name}:{job_id}"), job, workflow


def _shell(job: _Job, workflow: _Workflow) -> ShellLine | None:
    """Answer the shell a job's ``run:`` steps run under: its own default, else its workflow's."""
    for scope in (job.get("defaults", {}), workflow.get("defaults", {})):
        shell = scope.get("run", {}).get("shell")
        if shell is not None:
            return shell
    return None


def _uses(step: _Step, action: ActionRef) -> bool:
    return step.get("uses", "").startswith(action)


def test_every_run_step_of_every_workflow_is_declared() -> None:
    """No step runs that ``tools/_workflow_steps.py`` does not declare watched or exempt."""
    undeclared: list[tuple[Place, Prose]] = []
    for place, job, _workflow in _jobs():
        for step in job.get("steps", []):
            if "run" in step:
                declared = declared_for(step["run"])
                if not isinstance(declared, WorkflowStep):
                    undeclared.append((Place(f"{place}:{step.get('name', '?')}"), declared))
    assert not undeclared, undeclared


def test_every_job_that_checks_out_the_tree_runs_under_the_watchdog() -> None:
    """Its shell is ``tools.watch_step``; the tree and Python 3.14 precede its first run step."""
    checkout, setup_python = ActionRef("actions/checkout"), ActionRef("actions/setup-python")
    wrong: list[Place] = []
    for place, job, workflow in _jobs():
        steps = job.get("steps", [])
        first_run = next((i for i, step in enumerate(steps) if "run" in step), None)
        if first_run is None or not any(_uses(step, checkout) for step in steps):
            continue
        before = steps[:first_run]
        python = any(
            _uses(step, setup_python)
            and str(step.get("with", {}).get("python-version", "")).startswith("3.14")
            for step in before
        )
        checked_out = any(_uses(step, checkout) for step in before)
        if _shell(job, workflow) != _WATCHED_SHELL or not checked_out or not python:
            wrong.append(place)
    assert not wrong, wrong


def test_no_run_step_of_a_watched_job_leaves_the_wrapper_or_the_checkout_s_root() -> None:
    """No step names its own shell or directory, and no watched job runs in a container.

    A shell of its own runs a step outside the watchdog, and a directory of its own or a
    container leaves ``-m tools.watch_step`` without the checkout's ``tools`` package.
    """
    wrong: list[Place] = []
    for place, job, workflow in _jobs():
        if _shell(job, workflow) != _WATCHED_SHELL:
            continue
        if "container" in job:
            wrong.append(place)
        wrong.extend(
            Place(f"{place}:{step.get('name', '?')}")
            for step in job.get("steps", [])
            if "run" in step and ("shell" in step or "working-directory" in step)
        )
    assert not wrong, wrong


def test_a_job_that_checks_out_nothing_runs_github_s_shell_and_exempt_steps_only() -> None:
    """With no tree there is no tooling: GitHub's ``bash -e``, and every step exempt."""
    checkout = ActionRef("actions/checkout")
    wrong: list[Place] = []
    for place, job, workflow in _jobs():
        steps = job.get("steps", [])
        runs = [step["run"] for step in steps if "run" in step]
        if not runs or any(_uses(step, checkout) for step in steps):
            continue
        declared = [declared_for(script) for script in runs]
        exempt = all(isinstance(d, WorkflowStep) and d.progress is None for d in declared)
        if _shell(job, workflow) != _GITHUB_SHELL or not exempt:
            wrong.append(place)
    assert not wrong, wrong


def test_a_script_running_our_tooling_is_watched_one_running_two_or_nothing_known_refused() -> None:
    """Setup lines beside a watched tool leave it watched; two watched tools or none are refused."""
    with_setup = declared_for(ScriptText("set -euo pipefail\npython -m tools.check_pr_title x\n"))
    assert isinstance(with_setup, WorkflowStep)
    assert with_setup.progress is not None
    assert "check_pr_title" in with_setup.runs
    setup_only = declared_for(ScriptText("set -e\nsudo apt-get install -y valgrind\n"))
    assert isinstance(setup_only, WorkflowStep)
    assert setup_only.progress is None
    assert setup_only.why
    two = declared_for(ScriptText("cabal run shake -- build\ncmake -S cpp -B cpp/build\n"))
    assert isinstance(two, str)
    assert "more than one watched tool" in two
    unknown = declared_for(ScriptText("\nmake world\n"))
    assert isinstance(unknown, str)
    assert "no declaration" in unknown
    assert "make world" in unknown


@pytest.mark.parametrize(
    ("script", "line"),
    [
        ("python3.14 -m tools.run_ci --parallel", "  ▶ build …"),
        ("python3.14 -m tools.run_ci --parallel", "  ✓ build (0s)"),
        ("python3.14 -m tools.run_ci --parallel", "  ✗ agda gates FAILED (exit 1, 21s)"),
        ("python3.14 -m tools.run_ci --parallel", "  ⊘ check-reproducible-build skipped (set it)"),
        ("python3.14 -m tools.run_ci --parallel", "  ⋯ pytest: ............... [ 25%]"),
        ("bash benchmarks/run_all.sh --bench x", ">>> Running Python throughput benchmark..."),
        ("bash benchmarks/run_all.sh --bench x", "    Saved: python_throughput.json"),
        ("python3.14 -m tools.check_action_pins", "progress: 0/1 check-action-pins"),
    ],
)
def test_a_watched_step_reads_the_lines_its_tool_prints(script: ScriptText, line: Line) -> None:
    """Each line, taken from a run of the step's tool, is a progress report of the step."""
    declared = declared_for(script)
    assert isinstance(declared, WorkflowStep), declared
    assert declared.progress is not None
    assert declared.progress.reports(heard_line(Chunk(line.encode())))


def test_every_watched_kind_has_an_allowance_no_shorter_than_the_floor() -> None:
    """A watched step is stopped once it goes its allowance without a report, never sooner."""
    short = [
        step.runs
        for step in WATCHED
        if step.progress is None
        or step.progress.allowance is None
        or step.progress.allowance < ALLOWANCE_FLOOR
    ]
    assert not short, short


def test_the_sweep_run_as_one_step_outlasts_every_step_it_runs() -> None:
    """The sweep's own watchdog stops and names a stuck step before the step running the sweep."""
    sweep = declared_for(ScriptText("python3.14 -m tools.run_ci --parallel\n"))
    assert isinstance(sweep, WorkflowStep), sweep
    assert sweep.progress is not None
    assert sweep.progress.allowance is not None
    inner = [p.allowance for p in STEP_PROGRESS.values() if p.allowance is not None]
    assert inner
    assert sweep.progress.allowance > max(inner)
