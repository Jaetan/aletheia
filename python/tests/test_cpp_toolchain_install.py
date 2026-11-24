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
A job names every package it takes from an archive in its install, since a
later refresh of apt's lists would read the script's sources and wait on their
servers; a later step that must refresh runs apt through
``apt_without_toolchain.sh``, over every source but those.  A
cache key stands for one package list, since a cache hit installs what the
cache holds whatever the install names, and the script installs from its
cache only when every package it names ends installed.  The script refreshes
the lists only when its cache cannot install what it names, so a later step
installing from an archive refreshes them itself, and one weekly job installs
from an empty directory, where an archive's change of key shows.
"""

from __future__ import annotations

import os
import re
from pathlib import Path
from typing import NamedTuple, NewType, TypedDict, cast

import pytest
import yaml

from tools._common import CommandWord, find_executable, run_capture

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
# A binding's word, as a workflow's matrix names it.
BindingWord = NewType("BindingWord", str)
# A module directly under tools/, as `-m tools.<module>` runs it.
ToolModule = NewType("ToolModule", str)


class _With(TypedDict, total=False):
    path: CachePath
    key: CacheKey


# Functional, since `if` and `with` are keywords.
_Step = TypedDict(
    "_Step", {"uses": ActionRef, "run": ShellText, "if": IfExpression, "with": _With}, total=False
)
# A cache step's key, a package as an archive names it, a source file under
# /etc/apt/sources.list.d/, and a line a stand-in program logs.
CacheKey = NewType("CacheKey", str)
ArchivePackage = NewType("ArchivePackage", str)
SourceFile = NewType("SourceFile", str)
CallLine = NewType("CallLine", str)
# Where in a step's shell text something starts, -1 where it is absent.
TextOffset = NewType("TextOffset", int)
# The packages one install names, in its order.
type _PackageList = tuple[ArchivePackage, ...]


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
# The script a step after the toolchain install runs apt through.
_APT = _REPO / "cpp" / "toolchain" / "apt_without_toolchain.sh"
_APT_CALL = "cpp/toolchain/apt_without_toolchain.sh"
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
# The shim's cabal project, whose gcc-location line names the C compiler every
# C compile of the shim runs.
_SHIM_PROJECT = _REPO / "haskell-shim" / "cabal.project"
# The tools that start shake, and so build the shim.
_SHAKE_TOOLS = (
    ToolModule("check_build_incremental"),
    ToolModule("check_reproducible_build"),
    ToolModule("run_ci"),
)
# A tool's start of shake: an argument list naming `shake` then `--`.
_STARTS_SHAKE = re.compile(r'"shake",\s*"--"')
# A step building the shim: a shake target that builds the library, or a tool starting shake.
_BUILDS_THE_SHIM = re.compile(
    r"shake -- (?:--keep-going )?(?:build|dist|packages)\b"
    + rf"|-m tools\.(?:{'|'.join(map(re.escape, _SHAKE_TOOLS))})\b"
)
# A condition narrowed to one side of a binding, its `if` then `rest`.
_BINDING_SIDE = re.compile(r"(?P<rest>.+) && matrix\.binding (?P<side>==|!=) '(?P<binding>[a-z]+)'")
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

    The script refreshes them only when its cache cannot install what it
    names, so no later step can count on lists another step refreshed.
    """
    installs = 0
    for job in _jobs():
        for step in job.steps:
            run = step.get("run", ShellText(""))
            install = _first(run, CommandWord("install"))
            if install == -1:
                continue
            assert -1 < _first(run, CommandWord("update")) < install, job.label
            installs += 1
    assert installs > 0


def _first(run: ShellText, command: CommandWord) -> TextOffset:
    """Return where ``run`` first gives apt-get ``command``, directly or through the script."""
    found = re.search(rf"(?:apt-get|{re.escape(_APT_CALL)}) {command}\b", run)
    return TextOffset(-1 if found is None else found.start())


def _script_sources() -> list[SourceFile]:
    """Return the source files the script writes under /etc/apt/sources.list.d/."""
    text = _SCRIPT.read_text(encoding="utf-8")
    return [SourceFile(name) for name in re.findall(r"tee /etc/apt/sources\.list\.d/(\S+)", text)]


def test_no_step_after_the_toolchain_install_refreshes_its_sources() -> None:
    """A step after the script in its job runs apt only through the script beside it.

    A refresh reading the script's sources waits on their servers for any
    package, and a 503 from one fails the step.
    """
    through = 0
    for job in _jobs():
        runs = [step.get("run", "") for step in job.steps]
        installed = next(
            (at for at, run in enumerate(runs) if "cpp/toolchain/install.sh" in run), None
        )
        if installed is None:
            continue
        for run in runs[installed + 1 :]:
            assert "apt-get" not in run, job.label
            through += _APT_CALL in run
    assert through > 0


def test_apt_runs_through_the_script_over_every_source_but_the_install_s() -> None:
    """Every apt call of the script reads a copy of the sources without the install's files."""
    text = _APT.read_text(encoding="utf-8")
    assert sorted(re.findall(r"! -name (\S+)", text)) == sorted(_script_sources())
    calls = [line for line in text.splitlines() if "apt-get " in line and not line.startswith("#")]
    assert calls == ['sudo apt-get -o "Dir::Etc::SourceParts=$parts" "$@"']


def test_a_cache_key_stands_for_one_package_list() -> None:
    """Every install from one toolchain cache key names the same packages.

    A cache hit installs what the cache holds whatever the install names, so
    an install naming a package the key's other installs do not would find it
    missing from a cache they filled, and refresh from every archive to get it.
    """
    lists: dict[CacheKey, set[_PackageList]] = {}
    for job in _jobs():
        for at, step in enumerate(job.steps):
            if not _caches_the_toolchain(step):
                continue
            words = job.steps[at + 1].get("run", "").split()[2:]
            key = step.get("with", {}).get("key", CacheKey(""))
            lists.setdefault(key, set()).add(tuple(ArchivePackage(word) for word in words))
    assert lists
    assert {key: len(named) for key, named in lists.items()} == dict.fromkeys(lists, 1)


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


def _shim_compiler() -> SourcePackage:
    """Return the C compiler the shim's cabal project names, which is its package's name too."""
    text = _SHIM_PROJECT.read_text(encoding="utf-8")
    found = re.search(r"^\s*gcc-location:\s*(\S+)", text, re.MULTILINE)
    assert found is not None, f"{_SHIM_PROJECT} names no gcc-location"
    return SourcePackage(found.group(1))


def _runs_whenever(installs: list[_Step], build: _Step) -> bool:
    """Say whether the installs run whenever the build does.

    One does when it has no condition or the build's own; two do when they
    split the build's condition by a binding, one each side.
    """
    wanted = build.get("if")
    conditions = [install.get("if") for install in installs]
    if None in conditions or wanted in conditions:
        return True
    sides: dict[BindingWord, set[Prose]] = {}
    for condition in conditions:
        split = _BINDING_SIDE.fullmatch(condition) if condition is not None else None
        if split is not None and split["rest"] == wanted:
            sides.setdefault(BindingWord(split["binding"]), set()).add(Prose(split["side"]))
    return any(found == {"==", "!="} for found in sides.values())


def test_every_job_building_the_shim_installs_its_c_compiler_first() -> None:
    """A job building the FFI library installs the shim project's compiler whenever it builds.

    Every C compile of the shim runs that compiler, and a runner has none of it.
    """
    compiler = _shim_compiler()
    builds = 0
    for job in _jobs():
        for at, step in enumerate(job.steps):
            if not _BUILDS_THE_SHIM.search(step.get("run", "")):
                continue
            installs = [
                earlier
                for earlier in job.steps[:at]
                if _INSTALL.fullmatch(earlier.get("run", "").strip())
                and compiler in earlier.get("run", "").split()
            ]
            assert _runs_whenever(installs, step), f"{job.label}: {step.get('name', '')}"
            builds += 1
    assert builds > 0


def test_the_tools_read_as_building_the_shim_are_those_starting_shake() -> None:
    """A step running a tool is read as a build exactly when that tool's source starts shake."""
    starting = sorted(
        ToolModule(path.stem)
        for path in (_REPO / "tools").glob("*.py")
        if _STARTS_SHAKE.search(path.read_text(encoding="utf-8"))
    )
    assert starting == sorted(_SHAKE_TOOLS)
    assert all(_BUILDS_THE_SHIM.search(f"python3 -m tools.{tool}") for tool in _SHAKE_TOOLS)


def test_every_toolchain_install_brings_the_builds_the_upstream_check_holds() -> None:
    """Every install names libstdc++-15-dev, whose packages are the gcc-15 and gcc-16 builds.

    cpp/toolchain/check_upstream.sh, which ends every install, holds an
    installed llvm-toolchain-23, gcc-15 and gcc-16 build to its recorded
    upstream, and an install of clang-23 alone brings neither gcc build.
    """
    upstream = (_REPO / "cpp" / "toolchain" / "check_upstream.sh").read_text(encoding="utf-8")
    assert '"gcc-15 ' in upstream
    assert '"gcc-16 ' in upstream
    installs = 0
    for job in _jobs():
        for step in job.steps:
            run = step.get("run", "").strip()
            if _INSTALL.fullmatch(run) or _COLD_INSTALL.fullmatch(run):
                assert "libstdc++-15-dev" in run.split(), f"{job.label}: {run}"
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


_A_SHELL_RUNS_THE_SCRIPT = "only bash runs what the script does with its cache and the archives"
_KEY_FILES = ("apt.llvm.org.asc", "ubuntu-toolchain-r.asc")
# The stand-ins: sudo runs its command but writes nothing under /etc, dpkg and
# apt-get log their arguments, and dpkg-query answers installed for a package
# the test names.
_SUDO = """#!/bin/sh
case "$1" in
  tee) cat > /dev/null; exit 0 ;;
  install) exit 0 ;;
esac
exec "$@"
"""
_LOGGER = '#!/bin/sh\necho "$(basename "$0") $*" >> "$CALLS"\n'
# dpkg logs too, and fails when the test says the cache does not install whole.
_DPKG = _LOGGER + 'exit "${DPKG_EXIT:-0}"\n'
_QUERY = """#!/bin/sh
for last; do :; done
for package in $INSTALLED; do
  [ "$package" = "$last" ] && { printf installed; exit 0; }
done
exit 1
"""


def _copy_script(tmp_path: Path) -> Path:
    """Copy the script and its key files, with a check that passes, and return the copy."""
    toolchain = tmp_path / "toolchain"
    toolchain.mkdir()
    script = toolchain / "install.sh"
    _ = script.write_text(_SCRIPT.read_text(encoding="utf-8"), encoding="utf-8")
    for name in _KEY_FILES:
        _ = (toolchain / name).write_bytes((_SCRIPT.parent / name).read_bytes())
    check = toolchain / "check_upstream.sh"
    _ = check.write_text("#!/bin/sh\nexit 0\n", encoding="utf-8")
    script.chmod(0o755)
    check.chmod(0o755)
    return script


def _stand_ins(tmp_path: Path) -> Path:
    """Write the stand-in programs into a directory of their own, and return it."""
    bin_dir = tmp_path / "bin"
    bin_dir.mkdir()
    for name, text in (
        ("sudo", _SUDO),
        ("dpkg", _DPKG),
        ("apt-get", _LOGGER),
        ("dpkg-query", _QUERY),
    ):
        stand_in = bin_dir / name
        _ = stand_in.write_text(text, encoding="utf-8")
        stand_in.chmod(0o755)
    return bin_dir


def _run_script(
    tmp_path: Path,
    named: list[ArchivePackage],
    installed: list[ArchivePackage],
    *,
    dpkg_fails: bool = False,
) -> list[CallLine]:
    """Run the script on a cache holding one package, and return what reached dpkg and apt-get.

    dpkg-query answers ``installed`` for each of ``installed``, as after the
    cache's packages are installed.
    """
    script = _copy_script(tmp_path)
    cache = tmp_path / "cache"
    cache.mkdir()
    _ = (cache / "cached.deb").write_bytes(b"")
    calls = tmp_path / "calls"
    gnupg = tmp_path / "gnupg"
    gnupg.mkdir(mode=0o700)
    env = os.environ | {
        "PATH": f"{_stand_ins(tmp_path)}{os.pathsep}{os.environ['PATH']}",
        "CALLS": str(calls),
        "INSTALLED": " ".join(installed),
        "GNUPGHOME": str(gnupg),
        "DPKG_EXIT": "1" if dpkg_fails else "0",
    }
    result = run_capture([find_executable("bash"), str(script), str(cache), *named], env=env)
    assert result.returncode == 0, result.stderr
    return [CallLine(line) for line in calls.read_text(encoding="utf-8").splitlines()]


@pytest.mark.process(_A_SHELL_RUNS_THE_SCRIPT)
def test_a_cache_that_installs_every_named_package_reaches_no_archive(tmp_path: Path) -> None:
    """A warm run is dpkg over the cache alone: apt-get is never called."""
    named = [ArchivePackage("clang-23"), ArchivePackage("fish")]
    calls = _run_script(tmp_path, named, installed=named)
    assert calls == [CallLine(f"dpkg -i {tmp_path / 'cache' / 'cached.deb'}")]


@pytest.mark.process(_A_SHELL_RUNS_THE_SCRIPT)
def test_a_named_package_the_cache_lacks_is_installed_from_the_archives(tmp_path: Path) -> None:
    """A cache filled while the image carried a package leaves it out, and it is still installed.

    The script refreshes the lists and has apt install the missing package
    alone, rather than return with it missing or upgrade the installed ones.
    """
    named = [ArchivePackage("clang-23"), ArchivePackage("fish")]
    calls = _run_script(tmp_path, named, installed=[ArchivePackage("clang-23")])
    assert calls[1:] == [
        CallLine("apt-get update"),
        CallLine("apt-get -f install -y"),
        CallLine("apt-get install -y fish"),
    ]


@pytest.mark.process(_A_SHELL_RUNS_THE_SCRIPT)
def test_what_dpkg_leaves_broken_apt_fixes_named_no_package(tmp_path: Path) -> None:
    """A cache dpkg cannot install whole is fixed by apt, which does so only when named no package.

    Named packages, apt refuses with "Unmet dependencies", as an ubuntu:24.04
    container showed with a cache dpkg installed out of pre-dependency order.
    """
    named = [ArchivePackage("clang-23"), ArchivePackage("fish")]
    calls = _run_script(tmp_path, named, installed=named, dpkg_fails=True)
    assert calls[1:] == [CallLine("apt-get update"), CallLine("apt-get -f install -y")]
