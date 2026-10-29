# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
"""A check a workflow job runs is skipped only when what it reads was not made.

A step of a job is skipped once an earlier step failed, unless its ``if:``
says otherwise, so a job running several checks one after another reports
only the first that fails.  In each job holding more than one check, every
check waits on the steps making what it reads having passed, and on nothing
else, and a setup step placed after a check waits on the setup before it, so a
failing check stops no other while a failed setup still stops what reads it.
The steps that publish keep the default, so they run only once every step
before them passed.
"""

from __future__ import annotations

from typing import TYPE_CHECKING

from _workflows import JobName, StepId, StepIndex, StepName, every_job

if TYPE_CHECKING:
    from _workflows import Step


# The steps a check waits on, as their ids name them.
type WaitsOn = tuple[StepId, ...]

# Each job holding more than one check: each check, by the start of its name,
# and the steps it waits on.  The release-replay job of bundle-validation.yml
# is not here: its validation runs the downloaded bundle, which only a verified
# provenance makes safe to run, so it waits on every step before it.
_CHECKS: dict[JobName, dict[StepName, WaitsOn]] = {
    JobName("benchmark.yml:benchmark"): {
        StepName("Cross-binding benchmark-schema conformance"): (StepId("ready"),),
        StepName("Run the cross-language benchmark"): (StepId("ready"),),
        StepName("Regression gate"): (StepId("measure"),),
    },
    JobName("bundle-validation.yml:head-dist"): {
        StepName("Validate the bundle across the compiled bindings"): (StepId("ready"),),
        StepName("Self-test the validator"): (StepId("validate"),),
    },
    JobName("pr-heavy-lanes.yml:mutation-lane"): {
        StepName("mutmut operator facts"): (StepId("venv"),),
        StepName("cargo-mutants shard facts"): (
            StepId("cargo-mutants"),
            StepId("cargo-mutants-install"),
        ),
        StepName("Mutation testing"): (StepId("ready"),),
        StepName("Mull plugin facts"): (StepId("sweep"),),
        StepName("Whole-tree census"): (StepId("sweep"),),
    },
    JobName("pr-heavy-lanes.yml:mutation-merge"): {
        StepName("Merge the C++ legs"): (StepId("ready"),),
        StepName("Slices union"): (StepId("ready"),),
    },
    JobName("release.yml:release"): {
        StepName("Self-verify the signed tarball"): (StepId("dist"),),
        StepName("Smoke-test the bundle"): (StepId("dist"),),
        StepName("Validate the bundle across the compiled bindings"): (StepId("toolchains"),),
        StepName("Self-verify EVERY signed artifact"): (StepId("packages"),),
        StepName("Package install smoke"): (StepId("packages"),),
        StepName("Package payload structural check"): (StepId("packages"),),
        StepName("Build the runtime image"): (StepId("dist"), StepId("packages")),
    },
}

# The steps that publish, which run only once every step before them passed.
_PUBLISH: dict[JobName, tuple[StepName, ...]] = {
    JobName("release.yml:release"): (
        StepName("Publish the GitHub Release"),
        StepName("Push the runtime image to GHCR"),
    ),
}


def _named(steps: list[Step], start: StepName) -> StepIndex:
    """Return the position of the one step whose name starts with ``start``."""
    (position,) = (n for n, step in enumerate(steps) if step.get("name", "").startswith(start))
    return StepIndex(position)


def _runs_after_a_failure(step: Step) -> bool:
    """Say whether a step's condition lets it run after an earlier step failed."""
    condition = step.get("if", "")
    return "!cancelled()" in condition or "always()" in condition


def test_each_check_waits_on_what_it_reads_and_on_nothing_else() -> None:
    """Every check of the table runs after a failure and names the steps it waits on.

    Each of those steps runs before it.  The condition is a whole expression,
    `${{ }}` included, since a bare ``!cancelled()`` opens a YAML tag.
    """
    jobs = {job.label: job.steps for job in every_job()}
    assert set(_CHECKS) <= set(jobs)
    for label, checks in _CHECKS.items():
        steps = jobs[label]
        ids = [step.get("id") for step in steps]
        for start, waits_on in checks.items():
            position = _named(steps, start)
            condition = steps[position].get("if", "")
            assert condition.startswith("${{ "), (label, start, condition)
            assert condition.endswith(" }}"), (label, start, condition)
            assert "!cancelled()" in condition, (label, start, condition)
            for step_id in waits_on:
                assert f"steps.{step_id}." in condition, (label, start, step_id)
                assert ids.index(step_id) < position, (label, start, step_id)


def test_no_step_after_a_check_is_skipped_by_its_failure_but_the_publishing_ones() -> None:
    """Once a job's checks start, every step runs after a failure, the publishing ones apart.

    A setup step after a check would be skipped by that check's failure and
    take the checks needing it with it; a publishing step that ran after a
    failure would publish what a check refused.
    """
    jobs = {job.label: job.steps for job in every_job()}
    for label, checks in _CHECKS.items():
        steps = jobs[label]
        first = min(_named(steps, start) for start in checks)
        publish = {_named(steps, start) for start in _PUBLISH.get(label, ())}
        for position, step in enumerate(steps[first:], start=first):
            if position in publish:
                assert not _runs_after_a_failure(step), (label, step.get("name"))
            else:
                assert _runs_after_a_failure(step), (label, step.get("name"))
