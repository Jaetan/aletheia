# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
"""Every C++ toolchain install trusts its archives with the key files in ``cpp/toolchain/``.

The workflows install the toolchain through ``cpp/toolchain/install.sh``, and
the runtime image's verify stage copies the same key files, so no install
fetches a signing key: ``add-apt-repository`` asks Launchpad's API for the
PPA's key on every run, a keyserver or a key URL is one more server a run
depends on, and a timeout at any of them fails the job before anything of the
tree runs.  The image writes its own source lines, and they are the script's.
Both refuse a toolchain built from an upstream version ``check_upstream.sh``
does not record, whichever path installed it, since an evicted cache is filled
again with the archives' newest builds.
The script refreshes apt's lists only when its cache is empty, so every other
step installing from an archive refreshes them itself, and one weekly job
installs from an empty directory, where an archive's change of key shows.
"""

from __future__ import annotations

import os
import re
from pathlib import Path
from typing import NamedTuple, NewType, TypedDict, cast

import pytest
import yaml

from tools._common import find_executable, run_capture

from aletheia.common_types import ExitStatus, Prose

# A step's shell text, an action reference, its if: expression, a cache path, and a job's label.
ShellText = NewType("ShellText", str)
ActionRef = NewType("ActionRef", str)
IfExpression = NewType("IfExpression", str)
CachePath = NewType("CachePath", str)
JobName = NewType("JobName", str)
CronSpec = NewType("CronSpec", str)
# A source package, the upstream version of its build, and a line of dpkg-query's answer.
SourcePackage = NewType("SourcePackage", str)
UpstreamVersion = NewType("UpstreamVersion", str)
QueryLine = NewType("QueryLine", str)


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


class _Checked(NamedTuple):
    """How a run of the upstream check ended: its exit status and its annotations."""

    status: ExitStatus
    errors: Prose


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


_CHECK = _REPO / "cpp" / "toolchain" / "check_upstream.sh"
# A row of the check: a source package and the upstream version it records.
_ROW = re.compile(r'"([a-z][a-z0-9.+-]*) ([0-9][0-9A-Za-z.+-]*)"')
_CHECK_COPIED = "COPY cpp/toolchain/check_upstream.sh /usr/local/bin/"
_CHECK_RUN = "    check_upstream.sh && \\\n"
_LLVM = SourcePackage("llvm-toolchain-23")
_LIBSTDCXX = SourcePackage("gcc-15")
_RUNTIME = SourcePackage("gcc-16")
_A_SHELL_READS_THE_ANSWER = "only bash and awk answer what the check makes of dpkg-query's lines"


def _rows() -> dict[SourcePackage, UpstreamVersion]:
    """Return each source package the check records, with its upstream version."""
    (line,) = (
        line
        for line in _CHECK.read_text(encoding="utf-8").splitlines()
        if line.startswith("for entry in ")
    )
    return {SourcePackage(source): UpstreamVersion(ver) for source, ver in _ROW.findall(line)}


def _moved(upstream: UpstreamVersion) -> UpstreamVersion:
    """Return an upstream version after ``upstream``."""
    return UpstreamVersion(f"{upstream}.1")


def _answer(rows: dict[SourcePackage, UpstreamVersion]) -> list[QueryLine]:
    """Return dpkg-query's lines for ``rows``, each source installed at its version."""
    return [QueryLine(f"installed {source} {upstream}") for source, upstream in rows.items()]


def _check(tmp_path: Path, answer: list[QueryLine]) -> _Checked:
    """Run the check with a ``dpkg-query`` that answers ``answer``, and return how it ended."""
    lines = tmp_path / "answer"
    _ = lines.write_text("".join(f"{line}\n" for line in answer), encoding="utf-8")
    bin_dir = tmp_path / "bin"
    bin_dir.mkdir()
    query = bin_dir / "dpkg-query"
    _ = query.write_text(f"#!/bin/sh\nexec cat '{lines}'\n", encoding="utf-8")
    query.chmod(0o755)
    env = os.environ | {"PATH": f"{bin_dir}{os.pathsep}{os.environ['PATH']}"}
    result = run_capture([find_executable("bash"), str(_CHECK)], env=env)
    return _Checked(ExitStatus(result.returncode), Prose(result.stderr))


def test_the_check_records_each_source_of_the_toolchain() -> None:
    """The rows name LLVM, the libstdc++ 15 the workflows take, and the runtime it runs on."""
    assert sorted(_rows()) == sorted([_LLVM, _LIBSTDCXX, _RUNTIME])


@pytest.mark.process(_A_SHELL_READS_THE_ANSWER)
def test_a_rebuild_of_each_recorded_upstream_passes(tmp_path: Path) -> None:
    """A snapshot suffix after ``~`` is no new upstream, and an unrecorded source is not read."""
    rows = _rows()
    answer = [
        QueryLine(f"installed {_LLVM} {rows[_LLVM]}~++20260919103626+4b1925210476"),
        QueryLine(f"installed {_LLVM} {rows[_LLVM]}~++20260919103626+4b1925210476"),
        *_answer({source: upstream for source, upstream in rows.items() if source != _LLVM}),
        QueryLine("installed gcc-14 14.2.0"),
    ]
    assert _check(tmp_path, answer) == (0, "")


@pytest.mark.process(_A_SHELL_READS_THE_ANSWER)
def test_every_new_upstream_is_refused_naming_it(tmp_path: Path) -> None:
    """Each source installed at another upstream is named with what was found."""
    rows = _rows()
    moved = rows | {_LLVM: _moved(rows[_LLVM]), _LIBSTDCXX: _moved(rows[_LIBSTDCXX])}
    checked = _check(tmp_path, _answer(moved))
    assert checked.status == 1
    for source in (_LLVM, _LIBSTDCXX):
        assert (
            f"::error::{source} is installed at upstream {moved[source]}, not {rows[source]};"
            in checked.errors
        )
    assert f"::error::{_RUNTIME}" not in checked.errors


@pytest.mark.process(_A_SHELL_READS_THE_ANSWER)
def test_a_recorded_source_with_nothing_installed_is_refused(tmp_path: Path) -> None:
    """A runtime taken from another source leaves the recorded one with no installed package."""
    rows = _rows()
    answer = _answer({source: upstream for source, upstream in rows.items() if source != _RUNTIME})
    checked = _check(tmp_path, [*answer, QueryLine("installed gcc-17 17-20261001")])
    assert checked.status == 1
    assert (
        f"::error::{_RUNTIME} is installed at upstream none, not {rows[_RUNTIME]};"
        in checked.errors
    )


@pytest.mark.process(_A_SHELL_READS_THE_ANSWER)
def test_two_upstreams_of_one_source_are_refused_naming_both(tmp_path: Path) -> None:
    """Packages of one source at two upstreams are not the recorded toolchain, one matching or not.

    The annotation names both.
    """
    rows = _rows()
    later = _moved(rows[_RUNTIME])
    answer = [*_answer(rows), QueryLine(f"installed {_RUNTIME} {later}")]
    checked = _check(tmp_path, answer)
    assert checked.status == 1
    both = f"{rows[_RUNTIME]} {later}"
    assert (
        f"::error::{_RUNTIME} is installed at upstream {both}, not {rows[_RUNTIME]};"
        in checked.errors
    )


@pytest.mark.process(_A_SHELL_READS_THE_ANSWER)
def test_a_package_dpkg_does_not_hold_installed_is_not_read(tmp_path: Path) -> None:
    """dpkg-query lists removed packages too; one left at another upstream is no toolchain."""
    rows = _rows()
    leftover = QueryLine(f"config-files {_LIBSTDCXX} {_moved(rows[_LIBSTDCXX])}")
    assert _check(tmp_path, [*_answer(rows), leftover]) == (0, "")


def test_the_script_checks_the_upstream_after_every_install() -> None:
    """No install path leaves the script early, and its last command runs the check."""
    script = _SCRIPT.read_text(encoding="utf-8")
    assert "exit 0" not in script
    lines = [line for line in script.splitlines() if line]
    assert lines[-2:] == ['install_packages "$@"', '"$here/check_upstream.sh"']


def test_the_image_checks_the_upstream_after_its_install() -> None:
    """The verify stage copies the check and runs it once its toolchain is installed."""
    image = _DOCKERFILE.read_text(encoding="utf-8")
    assert _CHECK_COPIED in image
    install = image.index("apt-get install -y --no-install-recommends clang-23")
    assert _CHECK_RUN in image[install:]
