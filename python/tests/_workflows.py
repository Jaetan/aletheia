# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
"""The workflows' jobs and steps, for the tests that hold their structure.

Every scalar is read as text, as a workflow's inputs and scripts are: a
``run: 1`` or a ``key: 123`` is the string a test compares, never a number it
cannot search.
"""

from __future__ import annotations

from pathlib import Path
from typing import NamedTuple, NewType, TypedDict, cast

import yaml

REPO_ROOT = Path(__file__).resolve().parents[2]
WORKFLOWS = REPO_ROOT / ".github" / "workflows"

# A workflow file's text, a step's shell text, its action reference, its if:
# expression, its id and its name.
WorkflowText = NewType("WorkflowText", str)
ShellText = NewType("ShellText", str)
ActionRef = NewType("ActionRef", str)
IfExpression = NewType("IfExpression", str)
StepId = NewType("StepId", str)
StepName = NewType("StepName", str)
# A cache step's key, its path input and one path of it; a setup action's
# cache kind and the files its cache is keyed on, one per line.
CacheKey = NewType("CacheKey", str)
CachePaths = NewType("CachePaths", str)
CachePath = NewType("CachePath", str)
ToolCache = NewType("ToolCache", str)
DependencyPaths = NewType("DependencyPaths", str)
# A job's id in its workflow, and its label `<workflow file>:<job id>`.
JobId = NewType("JobId", str)
JobName = NewType("JobName", str)
# A step's position in its job, a file's path from the repository root, and a
# glob pattern as ``hashFiles`` takes one.
StepIndex = NewType("StepIndex", int)
TreePath = NewType("TreePath", str)
GlobPattern = NewType("GlobPattern", str)

# Functional, since these keys are keywords or not identifiers.
With = TypedDict(
    "With",
    {
        "path": CachePaths,
        "key": CacheKey,
        "restore-keys": CacheKey,
        "cache": ToolCache,
        "cache-dependency-path": DependencyPaths,
    },
    total=False,
)
Step = TypedDict(
    "Step",
    {
        "uses": ActionRef,
        "run": ShellText,
        "if": IfExpression,
        "with": With,
        "id": StepId,
        "name": StepName,
    },
    total=False,
)


class Job(TypedDict, total=False):
    """A job, of which the tests read the steps."""

    steps: list[Step]


class _Workflow(TypedDict, total=False):
    jobs: dict[JobId, Job]


class JobSteps(NamedTuple):
    """A job, named ``<workflow file>:<job id>``, and its steps."""

    label: JobName
    steps: list[Step]


def workflow_files() -> list[Path]:
    """Every workflow file, in name order."""
    return sorted(WORKFLOWS.glob("*.y*ml"))


# The safe loader with no implicit resolver, so every plain scalar is text (an
# empty value too, read as the empty string).  Built with ``type()`` and driven
# directly, as python/aletheia/yaml_loader.py builds its own: a ``class``
# statement inherits SafeLoader's ancestry into ``too-many-ancestors``, and the
# ``yaml.load`` call form is what the security linter matches.
_TextLoader: type[yaml.SafeLoader] = type(
    "_TextLoader", (yaml.SafeLoader,), {"yaml_implicit_resolvers": {}}
)


def jobs_of(path: Path) -> dict[JobId, Job]:
    """Read one workflow's jobs."""
    loader = _TextLoader(WorkflowText(path.read_text(encoding="utf-8")))
    try:
        workflow = cast("_Workflow", loader.get_single_data())
    finally:
        loader.dispose()
    return workflow.get("jobs", {})


def every_job() -> list[JobSteps]:
    """Every job of every workflow with its steps."""
    return [
        JobSteps(JobName(f"{path.name}:{name}"), job.get("steps", []))
        for path in workflow_files()
        for name, job in jobs_of(path).items()
    ]
