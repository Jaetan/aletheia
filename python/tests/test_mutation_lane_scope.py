# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
"""A mutation lane installs what its own sweep needs, and asks the runner which that is.

``tools.mutation_scope`` answers, for one binding, the question
``tools.mutation_run`` answers for all three, and it answers it from that same
function rather than from a second reading of the diff.  The heavy-lanes
workflow puts the question ahead of its toolchain steps and gates them on the
answer, so a lane whose binding no change touched installs nothing.

Two ways this goes wrong quietly and is held here: a toolchain step that keeps
no condition pays its minutes whatever the scope, and a cache save left
ungated writes a tree its restore never filled, because a skipped restore
reports an empty ``cache-hit`` which reads as a miss.
"""

from __future__ import annotations

from pathlib import Path
from typing import TYPE_CHECKING, cast

import pytest
import yaml

from tools import mutation_scope

if TYPE_CHECKING:
    from collections.abc import Callable

_WORKFLOW = Path(__file__).resolve().parents[2] / ".github" / "workflows" / "pr-heavy-lanes.yml"
_LANE_JOB = "mutation-lane"
_SWEEP_STEP = "Mutation testing (${{ matrix.lane }})"

# What a lane runs whatever its scope: the steps that reach the decision, and
# the steps that report.  Everything else is toolchain, and reads the decision.
# A step added here is a step whose minutes every lane pays.
_UNGATED_STEPS = (
    "Checkout (full history)",
    "Ensure a local `main` ref for `git diff main...HEAD`",
    "Set up Python 3.14",
    "Create the dev venv with the [mutation] extra (mutmut)",
    "Does this lane's binding sweep on this diff?",
    _SWEEP_STEP,
    "Upload the lane's reports",
)

type Step = dict[str, object]


def _steps() -> list[Step]:
    workflow = cast("dict[str, object]", yaml.safe_load(_WORKFLOW.read_text(encoding="utf-8")))
    jobs = cast("dict[str, dict[str, object]]", workflow["jobs"])
    return cast("list[Step]", jobs[_LANE_JOB]["steps"])


def _condition(step: Step) -> str:
    return str(step.get("if", ""))


def _reads_the_scope(step: Step) -> bool:
    return mutation_scope.SWEEPS_VAR in _condition(step)


def _gated_steps() -> list[tuple[str, Step]]:
    return [(str(step["name"]), step) for step in _steps() if _reads_the_scope(step)]


def test_the_steps_a_lane_runs_whatever_its_scope_are_the_ones_that_decide_and_report() -> None:
    """Every other step is toolchain, and reads the decision.

    A toolchain step with no condition costs its minutes on every lane.  Stated
    as the complement, because the list of things that install is one a
    new step joins without saying so: a `cp` from a cache directory installs as
    surely as an `apt-get`, and naming the installers is how such a step is
    missed.
    """
    ungated = tuple(str(step["name"]) for step in _steps() if not _reads_the_scope(step))
    assert ungated == _UNGATED_STEPS


def test_the_scope_is_read_the_way_an_absent_answer_installs() -> None:
    """`!= '0'` installs on an answer that did not arrive; `== '1'` would skip."""
    for name, step in _gated_steps():
        condition = _condition(step)
        assert f"{mutation_scope.SWEEPS_VAR} != '0'" in condition, f"{name}: {condition}"


def test_a_cache_save_reads_the_scope_its_restore_read() -> None:
    """A skipped restore reports no cache-hit, which reads as a miss and saves an empty tree."""
    saves = [
        (str(step["name"]), _condition(step))
        for step in _steps()
        if str(step.get("uses", "")).startswith("actions/cache/save")
    ]
    assert saves, "the lane saves no cache"
    for name, condition in saves:
        assert "cache-hit" in condition, f"{name} ignores its restore's outcome: {condition}"
        assert mutation_scope.SWEEPS_VAR in condition, f"{name} saves whatever the scope"


def test_the_sweep_itself_is_never_gated() -> None:
    """The lane runs the runner, reports and uploads whatever its scope.

    A gated sweep step would leave the required check reported by a job that ran
    nothing, and the C++ merge with a leg's reports missing.
    """
    sweep = next(step for step in _steps() if str(step.get("name")) == _SWEEP_STEP)
    assert not _condition(sweep)
    uploads = [step for step in _steps() if str(step.get("uses", "")).startswith("actions/upload")]
    assert uploads, "the lane uploads nothing"
    assert all(_condition(step) == "${{ always() }}" for step in uploads)


def test_the_lane_asks_the_tool_and_asks_it_before_it_installs() -> None:
    """One decision, taken by the runner's own function, ahead of every step that reads it."""
    names = [str(step["name"]) for step in _steps()]
    asking = [
        name
        for name, step in ((str(step["name"]), step) for step in _steps())
        if "tools.mutation_scope" in str(step.get("run", ""))
    ]
    assert len(asking) == 1, f"the scope is asked {len(asking)} times: {asking}"
    step = next(step for step in _steps() if str(step["name"]) == asking[0])
    assert "${{ matrix.binding }}" in str(step["run"]), "the lane does not name its own binding"
    asked_at = names.index(asking[0])
    first_gated = min(names.index(name) for name, _step in _gated_steps())
    assert asked_at < first_gated, f"{names[first_gated]} runs before the scope is known"


# What ``bindings_in_scope`` can answer, and what a lane sweeping C++ makes of it.
_SCOPE_CASES: list[tuple[set[str] | None, bool]] = [
    (None, True),  # the fail-safe answer: an empty diff, a global path, a git error
    ({"cpp"}, True),
    ({"python", "go"}, False),
    (set[str](), False),  # a documentation-only diff
]

# The same answers, as the line the workflow reads.
_WRITTEN_CASES: list[tuple[set[str] | None, str]] = [(None, "1"), (set[str](), "0")]


def _answering(in_scope: set[str] | None) -> Callable[[Path], set[str] | None]:
    """Return a stand-in for ``bindings_in_scope`` that answers ``in_scope``."""

    def answer(_repo_root: Path) -> set[str] | None:
        return in_scope

    return answer


@pytest.mark.parametrize(("in_scope", "expected"), _SCOPE_CASES)
def test_a_lane_sweeps_exactly_when_the_runner_would_run_its_binding(
    monkeypatch: pytest.MonkeyPatch, *, in_scope: set[str] | None, expected: bool
) -> None:
    """``lane_sweeps`` is ``bindings_in_scope`` read for one binding, including its None."""
    monkeypatch.setattr(mutation_scope, "bindings_in_scope", _answering(in_scope))
    assert mutation_scope.lane_sweeps("cpp", Path()) is expected


@pytest.mark.parametrize(("in_scope", "written"), _WRITTEN_CASES)
def test_the_answer_is_written_where_the_workflow_reads_it(
    monkeypatch: pytest.MonkeyPatch, tmp_path: Path, in_scope: set[str] | None, written: str
) -> None:
    """The decision lands in the file GITHUB_ENV names, appended, as one assignment."""
    monkeypatch.setattr(mutation_scope, "bindings_in_scope", _answering(in_scope))
    env_file = tmp_path / "github.env"
    _ = env_file.write_text("EXISTING=kept\n", encoding="utf-8")
    monkeypatch.setenv("GITHUB_ENV", str(env_file))
    assert mutation_scope.main(["--binding", "go"]) == 0
    assert env_file.read_text(encoding="utf-8") == (
        f"EXISTING=kept\n{mutation_scope.SWEEPS_VAR}={written}\n"
    )


def test_a_binding_no_runner_has_is_refused() -> None:
    """A lane naming an unknown binding must fail, not quietly skip its own toolchain."""
    with pytest.raises(SystemExit) as refusal:
        _ = mutation_scope.main(["--binding", "rust"])
    assert refusal.value.code == 2
