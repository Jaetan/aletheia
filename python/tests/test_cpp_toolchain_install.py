# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
"""Every C++ toolchain install trusts its archives with the key files in ``cpp/toolchain/``.

The workflows install the toolchain through ``cpp/toolchain/install.sh``, and
the runtime image's verify stage copies the same key files, so no install
fetches a signing key: ``add-apt-repository`` asks Launchpad's API for the
PPA's key on every run, a keyserver or a key URL is one more server a run
depends on, and a timeout at any of them fails the job before anything of the
tree runs.  The image writes its own source lines, and they are the script's.
The script refreshes apt's lists only when its cache is empty, so every other
step installing from an archive refreshes them itself, and one weekly job
installs from an empty directory, where an archive's change of key shows.
"""

from __future__ import annotations

import re
from pathlib import Path
from typing import NamedTuple, NewType, TypedDict, cast

import yaml

# A step's shell text, an action reference, its if: expression, a cache path, and a job's label.
ShellText = NewType("ShellText", str)
ActionRef = NewType("ActionRef", str)
IfExpression = NewType("IfExpression", str)
CachePath = NewType("CachePath", str)
JobName = NewType("JobName", str)
CronSpec = NewType("CronSpec", str)


class _With(TypedDict, total=False):
    path: CachePath


# Functional, since `if` and `with` are keywords.
_Step = TypedDict(
    "_Step", {"uses": ActionRef, "run": ShellText, "if": IfExpression, "with": _With}, total=False
)


class _Job(TypedDict, total=False):
    steps: list[_Step]


class _Workflow(TypedDict, total=False):
    jobs: dict[JobName, _Job]


class _Cron(TypedDict):
    cron: CronSpec


class _Triggers(TypedDict, total=False):
    schedule: list[_Cron]


# PyYAML reads a workflow's bare key `on` as the boolean True.
type _Triggered = dict[bool, _Triggers]


class _JobSteps(NamedTuple):
    """A job, named ``workflow:job``, and its steps."""

    label: JobName
    steps: list[_Step]


_REPO = Path(__file__).resolve().parents[2]
_WORKFLOWS = _REPO / ".github" / "workflows"
_SCRIPT = _REPO / "cpp" / "toolchain" / "install.sh"
_DOCKERFILE = _REPO / "Dockerfile.runtime"
# The directory the toolchain's packages are cached in, as every workflow names it.
_CACHE = CachePath("~/llvm-cache")
_INSTALL = re.compile(r"cpp/toolchain/install\.sh ~/llvm-cache( [a-z0-9.+-]+)+")
# The scheduled job that installs from an empty directory instead of the cache.
_COLD_WORKFLOW = "bundle-validation.yml"
_COLD_JOB = JobName(f"{_COLD_WORKFLOW}:release-replay")
_COLD_INSTALL = re.compile(
    r'cpp/toolchain/install\.sh "\$\{RUNNER_TEMP\}/llvm-cold"( [a-z0-9.+-]+)+'
)
# What fetches a signing key: the PPA helper, a keyserver, a key URL.
_FETCHES_A_KEY = ("add-apt-repository", "keyserver", "gpg.key")
_SOURCE_LINE = re.compile(r'"(deb [^"]+)"')
_KEYS_COPIED = (
    "COPY cpp/toolchain/apt.llvm.org.asc cpp/toolchain/ubuntu-toolchain-r.asc"
    " /etc/apt/trusted.gpg.d/"
)


def _jobs() -> list[_JobSteps]:
    """Return every job of every workflow with its steps."""
    jobs: list[_JobSteps] = []
    for path in sorted(_WORKFLOWS.glob("*.y*ml")):
        workflow = cast("_Workflow", yaml.safe_load(path.read_text(encoding="utf-8")))
        for name, job in workflow.get("jobs", {}).items():
            jobs.append(_JobSteps(JobName(f"{path.name}:{name}"), job.get("steps", [])))
    return jobs


def _caches_the_toolchain(step: _Step) -> bool:
    return step.get("uses", "").startswith("actions/cache@") and (
        step.get("with", {}).get("path") == _CACHE
    )


def test_no_install_fetches_a_signing_key() -> None:
    """No workflow and not the image asks a server for a key."""
    for path in [*sorted(_WORKFLOWS.glob("*.y*ml")), _DOCKERFILE]:
        text = path.read_text(encoding="utf-8")
        assert [word for word in _FETCHES_A_KEY if word in text] == [], path.name


def test_no_workflow_step_writes_an_apt_source_or_key() -> None:
    """The script is where the runners' sources and keys are written."""
    for job in _jobs():
        for step in job.steps:
            run = step.get("run", "")
            assert "sources.list.d" not in run, job.label
            assert "trusted.gpg.d" not in run, job.label


def test_every_workflow_apt_install_refreshes_the_lists_first() -> None:
    """A step installing from an archive refreshes apt's lists itself, before it installs.

    The script refreshes them only when its cache is empty, so no later step
    can count on lists another step refreshed.
    """
    installs = 0
    for job in _jobs():
        for step in job.steps:
            run = step.get("run", "")
            install = run.find("apt-get install")
            if install == -1:
                continue
            assert -1 < run.find("apt-get update") < install, job.label
            installs += 1
    assert installs > 0


def test_every_toolchain_cache_is_installed_by_the_script_under_its_condition() -> None:
    """The step after each restore of the cache runs the script on it, when the restore ran."""
    installs = 0
    for job in _jobs():
        for at, step in enumerate(job.steps):
            if "cpp/toolchain/install.sh" in step.get("run", "") and job.label != _COLD_JOB:
                assert at > 0, job.label
                assert _caches_the_toolchain(job.steps[at - 1]), job.label
            if not _caches_the_toolchain(step):
                continue
            install = job.steps[at + 1]
            assert _INSTALL.fullmatch(install.get("run", "").strip()), job.label
            assert install.get("if") == step.get("if"), job.label
            installs += 1
    assert installs > 0


def test_a_weekly_job_installs_from_an_empty_directory() -> None:
    """One scheduled job refreshes apt's lists and downloads every package, as no cached run does.

    A cached run reaches no server, so an archive that moves to another signing
    key would show only once a cache is rebuilt; this job shows it within a week.
    """
    text = (_WORKFLOWS / _COLD_WORKFLOW).read_text(encoding="utf-8")
    assert cast("_Triggered", yaml.safe_load(text))[True].get("schedule")
    (job,) = (job for job in _jobs() if job.label == _COLD_JOB)
    installs = [step for step in job.steps if "cpp/toolchain/install.sh" in step.get("run", "")]
    assert len(installs) == 1
    assert _COLD_INSTALL.fullmatch(installs[0].get("run", "").strip())
    assert not any(_caches_the_toolchain(step) for step in job.steps)


def test_the_image_trusts_the_script_keys_and_names_its_sources() -> None:
    """The verify stage copies the key files and writes the script's two source lines."""
    image = _DOCKERFILE.read_text(encoding="utf-8")
    assert _KEYS_COPIED in image
    script = _SCRIPT.read_text(encoding="utf-8")
    sources = set(_SOURCE_LINE.findall(script))
    assert len(sources) == 2
    assert set(_SOURCE_LINE.findall(image)) == sources
