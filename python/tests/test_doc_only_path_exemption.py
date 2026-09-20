# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
"""A documentation change skips the lanes no check requires, and only those.

A workflow path filter is a property of the whole file: it skips every job in
it, and a job that a filter skipped never reports, so a context the branch
ruleset requires would stay pending with nothing able to clear it.  That is why
the lanes carrying a required context and the lanes a documentation change
cannot move live in different files, and why the filter is held here: the set of
ignored paths is one set across the tree, no file carrying it defines a required
context, and the two lanes that exist to be skipped are in a file that carries
it on every event a diff reaches it by.
"""

from __future__ import annotations

from pathlib import Path
from typing import cast

import yaml

_WORKFLOWS = Path(__file__).resolve().parents[2] / ".github" / "workflows"

# The contexts the `main` ruleset requires (Settings, Rules, Rulesets; see
# docs/development/BRANCH_PR_HYGIENE.md).  GitHub keeps the ruleset outside the
# tree, so the names are stated here: a job of one of these names is what a path
# filter must never be able to skip.
_REQUIRED_CONTEXTS = frozenset({"tools/run_ci.py (all gates)", "mutation testing"})

# The lanes that own no required context, by job name.  Each one builds the
# whole tree and measures it, which a documentation change cannot move.
_EXEMPT_LANES = frozenset({"reproducible-build", "stability bench (advisory)"})

# workflow_dispatch takes no path filter and is not asked for one: a manual run
# is the escape hatch that reaches a lane whatever the diff.
_UNFILTERABLE_EVENTS = frozenset({"workflow_dispatch"})

# YAML 1.1 reads a bare ``on`` as the boolean it also spells, so a workflow
# mapping is keyed by a string everywhere but its trigger block.
type Workflow = dict[str | bool, object]
type Events = dict[str, dict[str, object] | None]


def _workflow(path: Path) -> Workflow:
    return cast("Workflow", yaml.safe_load(path.read_text(encoding="utf-8")))


def _events(workflow: Workflow) -> Events:
    """Return the workflow's trigger block, keyed by event name."""
    return cast("Events", workflow.get("on", workflow.get(True)))


def _ignored_paths(workflow: Workflow) -> dict[str, list[str]]:
    """Return the ignored-path list each of the workflow's events carries, by event."""
    return {
        event: cast("list[str]", spec["paths-ignore"])
        for event, spec in _events(workflow).items()
        if isinstance(spec, dict) and "paths-ignore" in spec
    }


def _job_names(workflow: Workflow) -> set[str]:
    """Return every context the workflow reports: a job's ``name``, or its key."""
    jobs = cast("dict[str, dict[str, object]]", workflow["jobs"])
    return {str(job.get("name", key)) for key, job in jobs.items()}


def _files() -> list[Path]:
    return sorted(_WORKFLOWS.glob("*.yml"))


def _filtered_files() -> list[Path]:
    return [path for path in _files() if _ignored_paths(_workflow(path))]


def test_every_documentation_exemption_in_the_tree_is_one_set() -> None:
    """One exemption, spelled the same everywhere.

    A second spelling is a lane skipped by a rule no other lane follows, and
    GitHub has no way to share a path list between workflows, so the lists are
    written twice and held equal here.
    """
    lists = {
        f"{path.name}:{event}": paths
        for path in _files()
        for event, paths in _ignored_paths(_workflow(path)).items()
    }
    assert lists, "no workflow carries a documentation exemption"
    distinct = {tuple(paths) for paths in lists.values()}
    assert len(distinct) == 1, f"the ignored-path lists disagree: {lists}"


def test_no_file_carrying_the_exemption_defines_a_required_context() -> None:
    """A required context a path filter can skip is a context that cannot clear."""
    for path in _filtered_files():
        required = _job_names(_workflow(path)) & _REQUIRED_CONTEXTS
        assert not required, f"{path.name} is path-filtered and defines {sorted(required)}"


def test_the_lanes_no_check_requires_are_the_ones_a_documentation_change_skips() -> None:
    """Both exempt lanes live in a filtered file, and neither event reaches them unfiltered.

    A filter on one event and not the other leaves half the cost standing.
    """
    filtered = _filtered_files()
    homes = {
        name: path for path in filtered for name in _job_names(_workflow(path)) & _EXEMPT_LANES
    }
    assert set(homes) == _EXEMPT_LANES, f"found {sorted(homes)} in a filtered workflow"
    for path in set(homes.values()):
        workflow = _workflow(path)
        unfiltered = set(_events(workflow)) - set(_ignored_paths(workflow)) - _UNFILTERABLE_EVENTS
        assert not unfiltered, f"{path.name} runs unfiltered on {sorted(unfiltered)}"
