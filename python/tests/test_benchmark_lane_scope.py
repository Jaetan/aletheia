# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
"""A benchmark leg always reports, and measures only what its diff can move.

``load scaling`` is a check the ``main`` ruleset requires, so ``benchmark.yml``
carries no path filter (``test_doc_only_path_exemption`` holds that): a workflow
a filter skips reports nothing, and a required check nothing reports holds a
pull request pending.  Each leg asks ``tools.benchmark_scope`` instead, which
reads the diff through the mutation runner's own ``bindings_in_scope`` with the
benchmark's global paths, and gates its toolchain, its measuring and its gate
on the answer.

Held here: what the question answers for each kind of diff, read from a real
branch of a throwaway repository; that the answer lands where the workflow
reads it; and the workflow's side, the steps that run whatever the answer, the
reading of the variable that measures when no answer arrived, and the question
asked once, before anything it gates.
"""

from __future__ import annotations

from pathlib import Path
from typing import NotRequired, TypedDict, cast

import pytest
import yaml
from _git_repo import commit, git

from tools import benchmark_scope
from tools._common import RelPath

from aletheia.common_types import Prose

_WORKFLOW = Path(__file__).resolve().parents[2] / ".github" / "workflows" / "benchmark.yml"
_QUESTION_STEP = Prose("Does this diff move a measurement?")
_NOTHING_STEP = Prose("Nothing to measure on this diff")

# What a leg runs whatever its scope: the steps that reach the decision, and the
# one that prints whatever was measured.  Everything else installs, builds,
# measures, gates or uploads, and reads the decision.
_UNGATED_STEPS = (
    Prose("Checkout (full history, for the diff the scope reads)"),
    Prose("Ensure a local `main` ref for `git diff main...HEAD`"),
    Prose("Set up Python 3.14"),
    Prose("Create the dev venv (python/.venv) with aletheia installed"),
    _QUESTION_STEP,
    Prose("Print the result JSON"),
)

# A workflow step, by the keys read here; `if` is a keyword, hence the call form.
# Every step of this workflow is named.
_Step = TypedDict(
    "_Step",
    {
        "name": Prose,
        "if": NotRequired[Prose],
        "run": NotRequired[Prose],
        "uses": NotRequired[Prose],
    },
)


class _Job(TypedDict):
    """The one job of the workflow, by the key read here."""

    steps: list[_Step]


class _Jobs(TypedDict):
    """The workflow's jobs."""

    benchmark: _Job


class _Workflow(TypedDict):
    """The workflow, by the key read here."""

    jobs: _Jobs


def _steps() -> list[_Step]:
    workflow = cast("_Workflow", yaml.safe_load(_WORKFLOW.read_text(encoding="utf-8")))
    return workflow["jobs"]["benchmark"]["steps"]


def _condition(step: _Step) -> Prose:
    return step.get("if", Prose(""))


def _reads_the_scope(step: _Step) -> bool:
    return benchmark_scope.MEASURES_VAR in _condition(step)


def test_the_steps_a_leg_runs_whatever_its_scope_are_the_ones_that_decide_and_print() -> None:
    """Every other step reads the decision; a step with no condition costs every leg its minutes."""
    ungated = tuple(step["name"] for step in _steps() if not _reads_the_scope(step))
    assert ungated == _UNGATED_STEPS


def test_the_scope_is_read_the_way_an_absent_answer_measures() -> None:
    """`!= '0'` measures when no answer arrived; `== '1'` would pass a required check unmeasured."""
    for step in _steps():
        if not _reads_the_scope(step) or step["name"] == _NOTHING_STEP:
            continue
        condition = _condition(step)
        assert f"{benchmark_scope.MEASURES_VAR} != '0'" in condition, f"{step['name']}: {condition}"


def test_a_leg_that_measures_nothing_says_so() -> None:
    """The one step on the other side of the answer: a green check says why nothing was measured."""
    step = next(step for step in _steps() if step["name"] == _NOTHING_STEP)
    assert _condition(step) == f"env.{benchmark_scope.MEASURES_VAR} == '0'"


def test_a_cache_save_reads_the_scope_its_restore_read() -> None:
    """A skipped restore reports no cache hit, which reads as a miss and saves an empty tree."""
    saves = [step for step in _steps() if step.get("uses", "").startswith("actions/cache/save")]
    assert saves, "the leg saves no cache"
    for step in saves:
        assert "cache-" in _condition(step), f"{step['name']} ignores its restore's outcome"
        assert _reads_the_scope(step), f"{step['name']} saves whatever the scope"


def test_the_leg_asks_once_and_before_anything_it_gates() -> None:
    """One decision, taken ahead of every step that reads it."""
    names = [step["name"] for step in _steps()]
    asking = [step["name"] for step in _steps() if "tools.benchmark_scope" in step.get("run", "")]
    assert asking == [_QUESTION_STEP]
    first_gated = min(names.index(step["name"]) for step in _steps() if _reads_the_scope(step))
    assert names.index(_QUESTION_STEP) < first_gated, f"{names[first_gated]} runs first"


def _branch_changing(tmp_path: Path, changed: tuple[RelPath, ...]) -> Path:
    """Return a repository on a branch off ``main`` whose one commit writes ``changed``."""
    repo = tmp_path / "repo"
    repo.mkdir()
    _ = git(repo, "init", "-q", "-b", "main")
    _ = (repo / "base.txt").write_text("base\n", encoding="utf-8")
    _ = commit(repo, "base")
    _ = git(repo, "checkout", "-q", "-b", "change")
    for rel in changed:
        path = repo / rel
        path.parent.mkdir(parents=True, exist_ok=True)
        _ = path.write_text("changed\n", encoding="utf-8")
    _ = commit(repo, "change")
    return repo


# Branches whose changes no leg measures on: documentation, and a gate no leg runs.
_UNMEASURED: tuple[tuple[RelPath, ...], ...] = (
    (RelPath("README.md"), RelPath("docs/development/BENCHMARKS.md")),
    (RelPath("tools/check_spdx_headers.py"),),
)

# Branches every leg measures on: the kernel, each binding, the harness, its
# schema check, its gate, this question, the diff reading it asks, the workflow.
_MEASURED: tuple[tuple[RelPath, ...], ...] = (
    (RelPath("src/Aletheia/DBC/Validator/Checks.agda"),),
    (RelPath("haskell-shim/src/AletheiaFFI.hs"),),
    (RelPath("python/benchmarks/scaling.py"),),
    (RelPath("go/aletheia/client.go"),),
    (RelPath("cpp/src/client.cpp"),),
    (RelPath("rust/src/backend.rs"),),
    (RelPath("benchmarks/run_all.sh"),),
    (RelPath("tools/check_bench_schema.py"),),
    (RelPath("tools/benchmark_gate.py"),),
    (RelPath("tools/benchmark_scope.py"),),
    (RelPath("tools/mutation_run.py"),),
    (RelPath(".github/workflows/benchmark.yml"),),
)


@pytest.mark.parametrize("changed", _UNMEASURED)
def test_a_branch_that_can_move_no_measurement_measures_nothing(
    monkeypatch: pytest.MonkeyPatch, tmp_path: Path, changed: tuple[RelPath, ...]
) -> None:
    """A change outside the kernel, the bindings and the benchmark's own files skips the leg."""
    monkeypatch.delenv("ALETHEIA_MUTATION_NO_DIFF_SCOPE", raising=False)
    assert not benchmark_scope.lane_measures(_branch_changing(tmp_path, changed))


@pytest.mark.parametrize("changed", _MEASURED)
def test_a_branch_that_can_move_a_measurement_measures(
    monkeypatch: pytest.MonkeyPatch, tmp_path: Path, changed: tuple[RelPath, ...]
) -> None:
    """The kernel, a binding, the harness, its gate and this question each measure."""
    monkeypatch.delenv("ALETHEIA_MUTATION_NO_DIFF_SCOPE", raising=False)
    assert benchmark_scope.lane_measures(_branch_changing(tmp_path, changed))


def test_a_branch_with_no_diff_measures(monkeypatch: pytest.MonkeyPatch, tmp_path: Path) -> None:
    """``main`` itself, after a merge, measures: the diff scope reads no change as everything."""
    monkeypatch.delenv("ALETHEIA_MUTATION_NO_DIFF_SCOPE", raising=False)
    repo = _branch_changing(tmp_path, (RelPath("docs/PITCH.md"),))
    _ = git(repo, "checkout", "-q", "main")
    assert benchmark_scope.lane_measures(repo)


@pytest.mark.parametrize("changed", [_UNMEASURED[0], _MEASURED[0]])
def test_the_answer_is_written_where_the_workflow_reads_it(
    monkeypatch: pytest.MonkeyPatch, tmp_path: Path, changed: tuple[RelPath, ...]
) -> None:
    """The decision lands in the file GITHUB_ENV names, appended, as one assignment."""
    monkeypatch.delenv("ALETHEIA_MUTATION_NO_DIFF_SCOPE", raising=False)
    measures = changed in _MEASURED
    monkeypatch.setattr(benchmark_scope, "REPO_ROOT", _branch_changing(tmp_path, changed))
    monkeypatch.setattr("sys.argv", ["benchmark_scope"])
    env_file = tmp_path / "github.env"
    _ = env_file.write_text("EXISTING=kept\n", encoding="utf-8")
    monkeypatch.setenv("GITHUB_ENV", str(env_file))
    assert benchmark_scope.main() == 0
    assert env_file.read_text(encoding="utf-8") == (
        f"EXISTING=kept\n{benchmark_scope.MEASURES_VAR}={int(measures)}\n"
    )
