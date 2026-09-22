# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
"""The cache-prune workflow runs the prune tool on the two paths, with the one write it needs.

``.github/workflows/cache-prune.yml`` prunes a closed pull request's own ref
when the request closes, and sweeps the whole store on a schedule and on
demand.  The wiring is held here because each half fails quietly on the
runner: a trigger left off never fires, a job without ``actions: write`` lists
and cannot delete, a run line that drops ``--apply`` prints a plan every day
and deletes nothing, and a closed request that is not routed to its own ref
falls through to a sweep that must ask the platform what the event already
said.
"""

from __future__ import annotations

import importlib
from pathlib import Path
from typing import cast

import yaml

_WORKFLOW = Path(__file__).resolve().parents[2] / ".github" / "workflows" / "cache-prune.yml"
_JOB = "prune"
_MODULE = "tools.prune_actions_cache"
# What the prune step is given, each the expression the workflow reads it from.
_ENV = (
    ("GH_TOKEN", "github.token"),
    ("GH_REPO", "github.repository"),
    ("CLOSED_PR_NUMBER", "github.event.pull_request.number"),
)

type Mapping = dict[str, object]


def _workflow() -> Mapping:
    return cast("Mapping", yaml.safe_load(_WORKFLOW.read_text(encoding="utf-8")))


def _triggers() -> Mapping:
    # PyYAML reads the bare key `on` as the boolean True.
    raw = cast("dict[object, object]", yaml.safe_load(_WORKFLOW.read_text(encoding="utf-8")))
    return cast("Mapping", raw.get("on", raw.get(True)))


def _job() -> Mapping:
    return cast("dict[str, Mapping]", _workflow()["jobs"])[_JOB]


def _run_lines() -> list[str]:
    steps = cast("list[Mapping]", _job()["steps"])
    return [str(step["run"]) for step in steps if "run" in step]


def test_a_closed_pull_request_a_schedule_and_a_dispatch_each_start_a_run() -> None:
    """The close is the prompt path; the schedule catches whatever a close could not delete."""
    triggers = _triggers()
    assert cast("Mapping", triggers["pull_request"])["types"] == ["closed"]
    schedule = cast("list[Mapping]", triggers["schedule"])
    assert len(schedule) == 1
    assert "cron" in schedule[0]
    assert "workflow_dispatch" in triggers


def test_the_workflow_reads_and_only_the_prune_job_writes_the_cache() -> None:
    """The top level grants nothing but read; the job adds the one scope a delete needs."""
    assert _workflow()["permissions"] == {"contents": "read"}
    job_permissions = cast("dict[str, str]", _job()["permissions"])
    assert job_permissions["actions"] == "write"
    assert [scope for scope, level in job_permissions.items() if level == "write"] == ["actions"]


def test_the_run_invokes_the_prune_module_with_apply_on_both_paths() -> None:
    """A closed request is routed to its own ref; every other event sweeps the store."""
    lines = _run_lines()
    assert len(lines) == 1
    run = lines[0]
    assert f'python3 -m {_MODULE} --apply --ref "refs/pull/${{CLOSED_PR_NUMBER}}/merge"' in run
    assert f"python3 -m {_MODULE} --apply\n" in run
    assert run.count(f"python3 -m {_MODULE}") == 2


def test_the_module_the_run_names_exists() -> None:
    """A rename of the tool is caught here rather than on the schedule."""
    assert importlib.import_module(_MODULE).main is not None


def test_the_prune_step_carries_the_token_the_repository_and_the_closed_request() -> None:
    """The CLI reads the token and the repository from its environment; the event names the ref."""
    steps = cast("list[Mapping]", _job()["steps"])
    prune = next(step for step in steps if "run" in step)
    assert prune["env"] == {name: "${{ " + expression + " }}" for name, expression in _ENV}
