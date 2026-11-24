# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
"""Run each test of a binding alone, in a process of its own.

No test depends on another (AGENTS.md, Universal Rules).  The Go and Catch2
suites run in an order of their own each run, which shows a test leaning on
another only on a seed that orders the pair badly; here every test of the
binding runs alone, where a test that needs another to run first fails every
time.  It runs where the branch moves the binding or this gate:

* Go: every package of the workspace's modules that has tests, its test binary
  built with ``go test -c``, each test, example and fuzz target run with
  ``-test.run '^Name$'`` in the package's directory;
* C++: every Catch2 suite ctest registers, read from ctest's own listing, each
  case run by name with the environment and the directory ctest gives it;
* Rust: every test binary cargo builds for the crate and for the excel crate,
  each test run with ``--exact``, one thread, and ``CARGO`` as cargo sets it.

Every run has the tree's library in ``ALETHEIA_LIB``, and the runs go side by
side, one per CPU the process may use.  A test that fails there is run once more
with none of the gate's other runs beside it: failing again, it leans on another
test; passing, it fails only beside other runs, sharing a file or a directory
with another test's process.  Both are findings, and the second run says which.

Run: ``python -m tools.check_tests_alone --binding go|cpp|rust``.  Exits 0 when
every test passes alone or the branch reaches none of the binding, 1 naming
each test that fails, alone or beside other runs, 2 when it cannot check: a
build fails, a binary lists no test, or a run runs none.
"""

from __future__ import annotations

import json
import os
import re
import sys
import tempfile
from concurrent.futures import ThreadPoolExecutor
from pathlib import Path
from typing import TYPE_CHECKING, Literal, NamedTuple, NewType, NotRequired, TypedDict, cast

from tools._branch_diff import branch_changes
from tools._common import (
    CommandWord,
    EnvName,
    EnvValue,
    ExecutorFactory,
    HelpText,
    RelPath,
    WorkerCount,
    binding_parser,
    emit,
    find_executable,
    run_capture,
)
from tools._progress import reporting

from aletheia.common_types import ExitStatus, Prose

if TYPE_CHECKING:
    from collections.abc import Callable

# A test's name as its runner lists it, what a run printed, a path as a tool
# prints it, a Go import path, and one ``NAME=value`` of ctest's.
TestName = NewType("TestName", str)
RunText = NewType("RunText", str)
PathText = NewType("PathText", str)
ImportPath = NewType("ImportPath", str)
EnvPair = NewType("EnvPair", str)
type Environment = dict[EnvName, EnvValue]
type Binding = Literal["go", "cpp", "rust"]
type TestRunner = Literal["go", "catch", "rust"]
type Verdict = Literal["passed", "failed", "ran none"]

REPO_ROOT = Path(__file__).resolve().parent.parent
BINDINGS: tuple[Binding, ...] = ("go", "cpp", "rust")
_GATE = RelPath("tools/check_tests_alone.py")
SCOPE_PATHS: dict[Binding, tuple[RelPath, ...]] = {
    "go": (RelPath("go/"), _GATE),
    "cpp": (RelPath("cpp/"), _GATE),
    "rust": (RelPath("rust/"), _GATE),
}
_GO_MODULES = (RelPath("go"), RelPath("go/excel"), RelPath("go/cmd/aletheia"))
_RUST_CRATES = (RelPath("rust"), RelPath("rust/excel"))
_GO_TEST = re.compile(r"^(?:Test|Example|Fuzz)\w*$")
# What a run that matched no test prints, by runner.
RAN_NONE = re.compile(r"testing: warning: no tests to run|No test cases matched|running 0 tests")
# What Catch2 prints for a case that skipped itself, which is no failure.
_SKIPPED = re.compile(r"test cases: 1 \| 1 skipped")
_W = CommandWord


class _CtestProperty(TypedDict):
    name: Prose
    value: list[EnvPair] | PathText


class _CtestTest(TypedDict):
    name: Prose
    command: NotRequired[list[CommandWord]]
    properties: NotRequired[list[_CtestProperty]]


class _CtestListing(TypedDict):
    tests: list[_CtestTest]


class _CargoProfile(TypedDict):
    test: bool


class _CargoTarget(TypedDict):
    name: Prose


class _CargoMessage(TypedDict, total=False):
    reason: Prose
    executable: PathText | None
    profile: _CargoProfile
    target: _CargoTarget


class Ran(NamedTuple):
    """A finished run: its exit status and everything it printed."""

    status: ExitStatus
    text: RunText


class Suite(NamedTuple):
    """One test binary: what it is called here, its tests, and where and how a test of it runs."""

    label: Prose
    tests: tuple[TestName, ...]
    binary: Path
    runner: TestRunner
    cwd: Path
    env: Environment


type SuiteReader = Callable[[Path], list[Suite]]


class Findings(NamedTuple):
    """What the runs found: tests failing alone, tests failing only beside others, empty runs."""

    alone: list[Prose]
    beside: list[Prose]
    empty: list[Prose]


class CannotCheckError(Exception):
    """The gate could not set up a run: a build failed or a binary listed no test."""


def in_scope(binding: Binding, changes: list[RelPath] | None) -> bool:
    """Whether the branch reaches ``binding``; no diff to read, or an empty one, does."""
    return not changes or any(path.startswith(SCOPE_PATHS[binding]) for path in changes)


def base_environment() -> Environment:
    """Return the process's environment with the tree's library named."""
    env = {EnvName(k): EnvValue(v) for k, v in os.environ.items()}
    env[EnvName("ALETHEIA_LIB")] = EnvValue(str(REPO_ROOT / "build" / "libaletheia-ffi.so"))
    return env


def capture(argv: list[CommandWord], cwd: Path, env: Environment) -> Ran:
    """Run ``argv`` and return its status and its output, both streams."""
    run = run_capture(argv, cwd=cwd, env=env)
    return Ran(ExitStatus(run.returncode), RunText(run.stdout + run.stderr))


def _words(*parts: Path | CommandWord) -> list[CommandWord]:
    return [CommandWord(str(part)) for part in parts]


def catch_spec(name: TestName) -> CommandWord:
    """Return a Catch2 test spec naming ``name`` alone, its special characters escaped."""
    return CommandWord(re.sub(r"([\\,\[\]*~\"])", r"\\\1", name))


def command_for(suite: Suite, name: TestName) -> list[CommandWord]:
    """Return the command running ``name`` of ``suite`` alone, as its runner selects one test."""
    match suite.runner:
        case "go":
            return _words(
                suite.binary, _W("-test.run"), _W(f"^{name}$"), _W("-test.count"), _W("1")
            )
        case "catch":
            return _words(suite.binary, catch_spec(name))
        case "rust":
            return _words(suite.binary, _W("--exact"), _W(name))


def _go_packages(go: CommandWord, module: Path, env: Environment) -> list[tuple[Path, ImportPath]]:
    """Return each package of ``module`` that has tests: its directory and its import path."""
    template = _W("{{.Dir}}\t{{.ImportPath}}\t{{len .TestGoFiles}}\t{{len .XTestGoFiles}}")
    listing = capture([go, _W("list"), _W("-f"), template, _W("./...")], module, env)
    if listing.status != 0:
        msg = f"go list in {module} exited {listing.status}: {listing.text[-300:]}"
        raise CannotCheckError(msg)
    packages: list[tuple[Path, ImportPath]] = []
    for line in listing.text.splitlines():
        pkg_dir, path, tests, xtests = line.split("\t")
        if (tests, xtests) != ("0", "0"):
            packages.append((Path(pkg_dir), ImportPath(path)))
    return packages


def go_suites(scratch: Path) -> list[Suite]:
    """Build every Go package's test binary; return each with its tests."""
    env = base_environment() | {EnvName("CGO_ENABLED"): EnvValue("1")}
    go = _W(find_executable("go"))
    suites: list[Suite] = []
    for module in _GO_MODULES:
        for pkg_dir, path in _go_packages(go, REPO_ROOT / module, env):
            binary = scratch / (re.sub(r"\W", "_", path) + ".test")
            built = capture(
                _words(go, _W("test"), _W("-c"), _W("-o"), binary, _W(path)),
                REPO_ROOT / module,
                env,
            )
            if built.status != 0:
                msg = f"go test -c {path} exited {built.status}: {built.text[-300:]}"
                raise CannotCheckError(msg)
            listed = capture(_words(binary, _W("-test.list"), _W(".*")), pkg_dir, env)
            names = tuple(TestName(n) for n in listed.text.split() if _GO_TEST.match(n))
            suites.append(Suite(Prose(path), names, binary, "go", pkg_dir, env))
    return suites


def _ctest_environment(test: _CtestTest) -> tuple[Environment, PathText | None]:
    """Return the environment ctest runs ``test`` in, and the directory it names, if one."""
    env = base_environment()
    directory: PathText | None = None
    for prop in test.get("properties", []):
        value = prop["value"]
        if prop["name"] == "ENVIRONMENT" and isinstance(value, list):
            for pair in value:
                key, _, setting = pair.partition("=")
                env[EnvName(key)] = EnvValue(setting)
        elif prop["name"] == "WORKING_DIRECTORY" and not isinstance(value, list):
            directory = value
    return env, directory


def cpp_suites(_scratch: Path) -> list[Suite]:
    """Read every Catch2 suite ctest registers, with ctest's environment and directory."""
    build = REPO_ROOT / "cpp" / "build"
    shown = capture(
        _words(_W(find_executable("ctest")), _W("--test-dir"), build, _W("--show-only=json-v1")),
        REPO_ROOT,
        base_environment(),
    )
    if shown.status != 0:
        msg = f"ctest --show-only exited {shown.status}: {shown.text[-300:]}"
        raise CannotCheckError(msg)
    suites: list[Suite] = []
    for test in cast("_CtestListing", json.loads(shown.text))["tests"]:
        command = test.get("command", [])
        # A Catch2 suite is registered shuffled (cpp/CMakeLists.txt); the rest are no suites.
        if command[1:] != [_W("--order"), _W("rand")]:
            continue
        env, directory = _ctest_environment(test)
        cwd = Path(directory) if directory is not None else build
        listed = capture([command[0], _W("--list-tests"), _W("--verbosity"), _W("quiet")], cwd, env)
        names = tuple(TestName(line) for line in listed.text.splitlines() if line.strip())
        if listed.status != 0 or not names:
            msg = f"{test['name']} listed no case (exit {listed.status})"
            raise CannotCheckError(msg)
        suites.append(Suite(test["name"], names, Path(command[0]), "catch", cwd, env))
    if not suites:
        msg = "ctest registers no Catch2 suite"
        raise CannotCheckError(msg)
    return suites


def rust_suites(_scratch: Path) -> list[Suite]:
    """Build every Rust test binary of both crates; return each with its tests."""
    cargo = _W(find_executable("cargo"))
    suites: list[Suite] = []
    for crate in _RUST_CRATES:
        cwd = REPO_ROOT / crate
        env = base_environment() | {
            EnvName("RUST_TEST_THREADS"): EnvValue("1"),
            EnvName("CARGO"): EnvValue(cargo),
            EnvName("CARGO_MANIFEST_DIR"): EnvValue(str(cwd)),
        }
        features = [_W("--all-features")] if crate == RelPath("rust") else []
        built = capture(
            [cargo, _W("test"), *features, _W("--no-run"), _W("--message-format=json")], cwd, env
        )
        if built.status != 0:
            msg = f"cargo test --no-run in {crate} exited {built.status}: {built.text[-300:]}"
            raise CannotCheckError(msg)
        for line in built.text.splitlines():
            if not line.startswith("{"):
                continue
            message = cast("_CargoMessage", json.loads(line))
            exe = message.get("executable")
            if message.get("reason") != "compiler-artifact" or exe is None:
                continue
            if not message.get("profile", {"test": False})["test"]:
                continue
            listed = capture([_W(exe), _W("--list"), _W("--format"), _W("terse")], cwd, env)
            names = tuple(
                TestName(entry.removesuffix(": test"))
                for entry in listed.text.splitlines()
                if entry.endswith(": test")
            )
            label = Prose(f"{crate}:{message.get('target', {'name': Prose('?')})['name']}")
            suites.append(Suite(label, names, Path(exe), "rust", cwd, env))
    return suites


SUITES: dict[Binding, SuiteReader] = {"go": go_suites, "cpp": cpp_suites, "rust": rust_suites}


def verdict(ran: Ran) -> Verdict:
    """Read one run alone: a case Catch2 skipped passes, and a run matching no test ran none."""
    if RAN_NONE.search(ran.text):
        return "ran none"
    if ran.status == 0 or _SKIPPED.search(ran.text):
        return "passed"
    return "failed"


def run_alone(
    suites: list[Suite], workers: WorkerCount, executor: ExecutorFactory = ThreadPoolExecutor
) -> Findings:
    """Run every test alone; return the tests that failed, and how, and the runs of no test.

    The runs go side by side on what ``executor`` builds for ``workers``; each
    test failing there is then run once more with none of them beside it.
    """
    jobs = [(suite, name) for suite in suites for name in suite.tests]
    found = Findings([], [], [])
    failing: list[tuple[Suite, TestName]] = []

    def one(job: tuple[Suite, TestName]) -> Ran:
        suite, name = job
        return capture(command_for(suite, name), suite.cwd, suite.env)

    emit(f"check_tests_alone: {len(jobs)} tests of {len(suites)} binaries, each alone")
    with executor(workers) as pool:
        runs = zip(jobs, pool.map(one, jobs), strict=True)
        for done, ((suite, name), ran) in enumerate(runs, 1):
            seen = verdict(ran)
            if seen == "ran none":
                found.empty.append(Prose(f"{suite.label} :: {name}"))
                emit(f"check_tests_alone: ran no test: {suite.label} :: {name}")
            elif seen == "failed":
                failing.append((suite, name))
            if done % 100 == 0:
                emit(f"check_tests_alone: {done}/{len(jobs)} run")
    _name_failures(failing, found)
    return found


def _name_failures(failing: list[tuple[Suite, TestName]], found: Findings) -> None:
    """Run each failing test once more with none beside it, and file it where that run says."""
    for suite, name in failing:
        test = Prose(f"{suite.label} :: {name}")
        again = capture(command_for(suite, name), suite.cwd, suite.env)
        if verdict(again) == "passed":
            found.beside.append(test)
            emit(f"check_tests_alone: FAILS BESIDE OTHER RUNS {test}: passes with none beside it")
        else:
            found.alone.append(test)
            tail = " | ".join(again.text.strip().splitlines()[-4:])
            emit(f"check_tests_alone: FAILS ALONE {test}: {tail}")


def main(
    argv: list[CommandWord] | None = None, executor: ExecutorFactory = ThreadPoolExecutor
) -> ExitStatus:
    """Run every test of the named binding alone where the branch reaches it."""
    parser = binding_parser(BINDINGS, HelpText(__doc__ or ""))
    binding = cast("Binding", parser.parse_args(argv).binding)
    if not in_scope(binding, branch_changes(REPO_ROOT)):
        emit(f"check_tests_alone: no change on the branch reaches the {binding} binding")
        return ExitStatus(0)
    with tempfile.TemporaryDirectory(prefix=f"aletheia-tests-alone-{binding}-") as scratch:
        try:
            suites = SUITES[binding](Path(scratch))
        except CannotCheckError as error:
            emit(f"check_tests_alone: {binding}: cannot check: {error}")
            return ExitStatus(2)
        workers = WorkerCount(max(1, len(os.sched_getaffinity(0))))
        found = run_alone(suites, workers, executor)
    if found.empty:
        emit(f"check_tests_alone: {binding}: {len(found.empty)} runs ran no test, unchecked")
        return ExitStatus(2)
    if found.alone or found.beside:
        emit(
            f"check_tests_alone: {binding}: {len(found.alone)} tests fail alone, each leaning on"
            + f" another; {len(found.beside)} fail only beside other runs, each sharing a file"
            + " or a directory with another test's process"
        )
        return ExitStatus(1)
    emit(f"check_tests_alone: every {binding} test passes alone")
    return ExitStatus(0)


if __name__ == "__main__":
    sys.exit(reporting(main, Prose("check-tests-alone")))
