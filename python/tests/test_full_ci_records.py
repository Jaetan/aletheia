# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
"""The full-CI job writes its sweep's log under the runner's temporary directory and uploads it.

``tools.run_ci`` writes its log where ``ALETHEIA_CI_OUTPUT`` names, so each
step running the sweep names an absolute place under ``runner.temp``, outside
the checkout, and the job's upload reads the log from that place: an upload
naming any other directory finds no log and only warns.
"""

from __future__ import annotations

from pathlib import Path
from typing import NewType, NotRequired, TypedDict, cast

import yaml

from tools._common import EnvName, EnvValue
from tools._records import RECORDS_ENV

from aletheia.common_types import Prose

_WORKFLOW = Path(__file__).resolve().parents[2] / ".github" / "workflows" / "pr-full-ci.yml"
# What a step running the sweep runs, the action an upload step uses, and the
# expression naming the runner's temporary directory, an absolute path.
_SWEEP = Prose("-m tools.run_ci")
_UPLOAD = Prose("actions/upload-artifact@")
_RUNNER_TEMP = EnvValue("${{ runner.temp }}/")
# The name of the files the sweep writes in the records directory.
_LOGS = "*.log"

_JobId = NewType("_JobId", str)


class _Inputs(TypedDict):
    """An upload step's inputs, by the key read here."""

    path: NotRequired[Prose]


# A workflow step, by the keys read here; `with` is a keyword, hence the call form.
_Step = TypedDict(
    "_Step",
    {
        "run": NotRequired[Prose],
        "uses": NotRequired[Prose],
        "env": NotRequired[dict[EnvName, EnvValue]],
        "with": NotRequired[_Inputs],
    },
)


class _Job(TypedDict):
    """A job of the workflow, by the key read here."""

    steps: list[_Step]


class _Workflow(TypedDict):
    """The workflow, by the key read here."""

    jobs: dict[_JobId, _Job]


def _jobs() -> list[_Job]:
    workflow = cast("_Workflow", yaml.safe_load(_WORKFLOW.read_text(encoding="utf-8")))
    return list(workflow["jobs"].values())


def _sweeps(job: _Job) -> list[_Step]:
    return [step for step in job["steps"] if _SWEEP in step.get("run", Prose(""))]


def _records(step: _Step) -> EnvValue | None:
    return step.get("env", {}).get(RECORDS_ENV)


def test_each_sweep_names_a_records_directory_under_the_runner_temp() -> None:
    """Each step running the sweep sets the variable to an absolute place outside the checkout."""
    sweeps = [step for job in _jobs() for step in _sweeps(job)]
    assert sweeps, f"no step of {_WORKFLOW.name} runs {_SWEEP}"
    named = [_records(step) for step in sweeps]
    assert all(value is not None and value.startswith(_RUNNER_TEMP) for value in named), named


def test_the_job_uploads_the_log_from_the_records_directory_its_sweep_names() -> None:
    """A job running the sweep uploads, after it, the logs in the directory the sweep wrote to."""
    jobs = [job for job in _jobs() if _sweeps(job)]
    assert jobs, f"no job of {_WORKFLOW.name} runs {_SWEEP}"
    for job in jobs:
        steps = job["steps"]
        (sweep,) = _sweeps(job)
        uploads = [step for step in steps if step.get("uses", Prose("")).startswith(_UPLOAD)]
        read = [step.get("with", _Inputs()).get("path") for step in uploads]
        assert read == [f"{_records(sweep)}/{_LOGS}"], read
        assert steps.index(sweep) < steps.index(uploads[0]), "the upload runs after the sweep"
