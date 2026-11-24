# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
"""Each Go, C++ and Rust test runs alone where a branch moves its binding.

``tools/check_tests_alone.py`` runs every test of a binding in a process of its
own, so a test that leans on another having run first fails every time.  These
tests hold its scope, the command each runner selects one test with, how a run
is read, the findings it names, the status it exits with, and its registration.
"""

from __future__ import annotations

import subprocess
from pathlib import Path

import pytest
from _ci_runner import ci_runner
from _executors import DrivenExecutor

from tools import check_tests_alone
from tools._ci_steps import register_all_steps
from tools._common import (
    BUILD_STEP,
    CARGO_TEST_BUILD_STEP,
    CPP_BUILD_STEP,
    EXCEL_CARGO_TEST_BUILD_STEP,
    CommandWord,
    EnvName,
    EnvValue,
    HelpText,
    RelPath,
    WorkerCount,
    binding_parser,
)
from tools.check_tests_alone import (
    CannotCheckError,
    Environment,
    Ran,
    RunText,
    Suite,
    TestName,
    Verdict,
    catch_spec,
    command_for,
    in_scope,
    run_alone,
    verdict,
)

from aletheia.common_types import ExitStatus, Prose

_BINARY = Path("/bin/suite")
_A, _B, _C, _D = TestName("TestA"), TestName("TestB"), TestName("TestC"), TestName("TestD")


def _suite(runner: check_tests_alone.TestRunner) -> Suite:
    return Suite(Prose("pkg"), (_A, _B, _C, _D), _BINARY, runner, Path("/"), {})


def test_a_branch_reaches_a_binding_by_its_tree_or_the_gate() -> None:
    """A binding's own tree or the gate reaches it; a document, or another binding, does not."""
    for binding in check_tests_alone.BINDINGS:
        assert in_scope(binding, None)
        assert in_scope(binding, [])
        assert in_scope(binding, [RelPath("tools/check_tests_alone.py")])
        assert not in_scope(binding, [RelPath("docs/README.md")])
    assert in_scope("go", [RelPath("go/aletheia/client_test.go")])
    assert in_scope("cpp", [RelPath("cpp/tests/temp_path.hpp")])
    assert in_scope("rust", [RelPath("rust/tests/lifecycle.rs")])
    assert not in_scope("go", [RelPath("rust/src/lib.rs")])


def test_each_runner_selects_one_test_by_its_name() -> None:
    """Go anchors the name, Catch2 takes it as a spec, and libtest matches it exactly."""
    assert command_for(_suite("go"), _A) == [
        CommandWord("/bin/suite"),
        CommandWord("-test.run"),
        CommandWord("^TestA$"),
        CommandWord("-test.count"),
        CommandWord("1"),
    ]
    assert command_for(_suite("catch"), TestName("a case")) == [
        CommandWord("/bin/suite"),
        CommandWord("a case"),
    ]
    assert command_for(_suite("rust"), TestName("m::t")) == [
        CommandWord("/bin/suite"),
        CommandWord("--exact"),
        CommandWord("m::t"),
    ]


def test_a_catch2_spec_escapes_what_catch2_reads_as_syntax() -> None:
    """A comma, brackets, a star, a tilde, a quote and a backslash in a name are taken literally."""
    assert catch_spec(TestName('a, b [c] *d ~e "f" \\g')) == CommandWord(
        'a\\, b \\[c\\] \\*d \\~e \\"f\\" \\\\g'
    )


@pytest.mark.parametrize(
    ("ran", "seen"),
    [
        (Ran(ExitStatus(0), RunText("ok")), "passed"),
        (Ran(ExitStatus(1), RunText("--- FAIL: TestA")), "failed"),
        (Ran(ExitStatus(4), RunText("test cases: 1 | 1 skipped")), "passed"),
        (Ran(ExitStatus(0), RunText("testing: warning: no tests to run")), "ran none"),
        (Ran(ExitStatus(2), RunText("No test cases matched 'x'")), "ran none"),
        (Ran(ExitStatus(0), RunText("running 0 tests")), "ran none"),
    ],
)
def test_a_run_is_read_as_passed_failed_or_running_none(ran: Ran, seen: Verdict) -> None:
    """A Catch2 skip passes, and a run that matched no test is no pass."""
    assert verdict(ran) == seen


_PASSED = Ran(ExitStatus(0), RunText("ok"))
_FAILED = Ran(ExitStatus(1), RunText("--- FAIL"))
_RAN_NONE = Ran(ExitStatus(0), RunText("testing: warning: no tests to run"))
# Each test's runs in turn: B fails beside the other runs and alone, D only beside them.
_RUNS = {_A: (_PASSED,), _B: (_FAILED, _FAILED), _C: (_RAN_NONE,), _D: (_FAILED, _PASSED)}


def _answering(monkeypatch: pytest.MonkeyPatch) -> None:
    """Answer each run by the test its command selects, that test's runs in turn."""
    queues = {name: list(runs) for name, runs in _RUNS.items()}

    def ran(argv: list[CommandWord], cwd: Path, env: Environment) -> Ran:
        del cwd, env
        return queues[TestName(argv[2].strip("^$"))].pop(0)

    monkeypatch.setattr(check_tests_alone, "capture", ran)


def test_every_test_runs_alone_and_each_finding_is_named(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    """A test failing alone, one failing only beside other runs, and an empty run are named."""
    _answering(monkeypatch)
    found = run_alone([_suite("go")], WorkerCount(2), DrivenExecutor)
    assert found.alone == [Prose("pkg :: TestB")]
    assert found.beside == [Prose("pkg :: TestD")]
    assert found.empty == [Prose("pkg :: TestC")]


def _reader_of(names: tuple[TestName, ...]) -> check_tests_alone.SuiteReader:
    def read(_scratch: Path) -> list[Suite]:
        return [Suite(Prose("pkg"), names, _BINARY, "go", Path("/"), {})]

    return read


def _cannot_read(_scratch: Path) -> list[Suite]:
    msg = "a build failed"
    raise CannotCheckError(msg)


def _changes_in_go(_root: Path) -> list[RelPath]:
    return [RelPath("go/aletheia/client.go")]


def _changes_elsewhere(_root: Path) -> list[RelPath]:
    return [RelPath("docs/x.md")]


@pytest.mark.parametrize(
    ("reader", "status"),
    [
        (_reader_of((_A,)), ExitStatus(0)),
        (_reader_of((_A, _B)), ExitStatus(1)),
        (_reader_of((_A, _D)), ExitStatus(1)),
        (_reader_of((_A, _C)), ExitStatus(2)),
        (_cannot_read, ExitStatus(2)),
    ],
)
def test_the_status_says_passed_failed_or_could_not_check(
    monkeypatch: pytest.MonkeyPatch, reader: check_tests_alone.SuiteReader, status: ExitStatus
) -> None:
    """0 when every test passes, 1 when one fails alone or beside others, 2 when it cannot check."""
    monkeypatch.setattr(check_tests_alone, "branch_changes", _changes_in_go)
    _answering(monkeypatch)
    monkeypatch.setitem(check_tests_alone.SUITES, "go", reader)
    argv = [CommandWord("--binding"), CommandWord("go")]
    assert check_tests_alone.main(argv, DrivenExecutor) == status


def test_a_branch_reaching_no_binding_runs_nothing(monkeypatch: pytest.MonkeyPatch) -> None:
    """Out of scope, the gate says so and exits 0 without building a binary."""
    monkeypatch.setattr(check_tests_alone, "branch_changes", _changes_elsewhere)
    for binding in check_tests_alone.BINDINGS:
        monkeypatch.setitem(check_tests_alone.SUITES, binding, _cannot_read)
        assert check_tests_alone.main([CommandWord("--binding"), CommandWord(binding)]) == 0


def test_every_sweep_runs_each_binding_s_tests_alone_in_its_lane(tmp_path: Path) -> None:
    """Each binding's alone run is a step of its lane, after the builds its tests come from."""
    runner = ci_runner(tmp_path)
    register_all_steps(runner, ["cabal", "run", "shake", "--"], runner.opts)
    steps = {step.name: step for step in runner.registered_steps}
    expected = {
        "go": ("misc", (BUILD_STEP,)),
        "cpp": ("cpp", (BUILD_STEP, CPP_BUILD_STEP)),
        "rust": ("rust", (BUILD_STEP, CARGO_TEST_BUILD_STEP, EXCEL_CARGO_TEST_BUILD_STEP)),
    }
    for binding, (lane, needs) in expected.items():
        step = steps[f"check-tests-alone-{binding}"]
        assert step.cmd == [runner.python, "-m", "tools.check_tests_alone", "--binding", binding]
        assert step.lane == lane
        assert tuple(step.needs) == needs


def test_a_binding_gate_takes_the_binding_named_and_refuses_another() -> None:
    """``--binding`` names one of the gate's bindings; argparse refuses any other, exiting 2."""
    parser = binding_parser(check_tests_alone.BINDINGS, HelpText(""))
    assert parser.parse_args([CommandWord("--binding"), CommandWord("rust")]).binding == "rust"
    with pytest.raises(SystemExit) as refused:
        _ = parser.parse_args([CommandWord("--binding"), CommandWord("java")])
    assert refused.value.code == 2


def _tool_at(_name: CommandWord) -> CommandWord:
    return CommandWord("/bin/tool")


def test_go_listings_are_read_from_their_output_alone(
    monkeypatch: pytest.MonkeyPatch, tmp_path: Path
) -> None:
    """``go: downloading`` on the error stream, as a cold module cache prints it, lists nothing.

    Nor does a name there that looks like a test's.
    """
    package = RunText(f"{tmp_path}\texample.com/m/p\t1\t0\n")
    tests = RunText("TestA\nTestB\nBenchmarkC\n")

    def ran(argv: list[CommandWord], cwd: Path, env: Environment) -> Ran:
        del cwd, env
        if argv[1] == "list":
            return Ran(ExitStatus(0), RunText(f"go: downloading x v1\n{package}"), package)
        if argv[1] == "-test.list":
            return Ran(ExitStatus(0), RunText(f"TestNoise\n{tests}"), tests)
        return Ran(ExitStatus(0), RunText(""), RunText(""))

    monkeypatch.setattr(check_tests_alone, "find_executable", _tool_at)
    monkeypatch.setattr(check_tests_alone, "capture", ran)
    suites = check_tests_alone.go_suites(tmp_path)
    assert [suite.tests for suite in suites] == [(_A, _B)] * 3
    assert {suite.runner for suite in suites} == {"go"}


def test_ctest_listings_are_read_from_their_output_alone(monkeypatch: pytest.MonkeyPatch) -> None:
    """A word on ctest's or Catch2's error stream is neither JSON nor a case name."""
    listing = RunText(
        '{"tests": [{"name": "unit_tests", "command": ["/b/unit_tests", "--order", "rand"],'
        + ' "properties": [{"name": "ENVIRONMENT", "value": ["K=v"]},'
        + ' {"name": "WORKING_DIRECTORY", "value": "/w"}]},'
        + ' {"name": "static_tests", "command": ["/b/static_tests"]}]}'
    )
    cases = RunText("a case\n")

    def ran(argv: list[CommandWord], cwd: Path, env: Environment) -> Ran:
        if argv[-1] == "--show-only=json-v1":
            return Ran(ExitStatus(0), RunText(f"ctest: a warning\n{listing}"), listing)
        assert cwd == Path("/w")
        assert env[EnvName("K")] == EnvValue("v")
        return Ran(ExitStatus(0), RunText(f"a warning\n{cases}"), cases)

    monkeypatch.setattr(check_tests_alone, "find_executable", _tool_at)
    monkeypatch.setattr(check_tests_alone, "capture", ran)
    suites = check_tests_alone.cpp_suites(Path("/scratch"))
    assert len(suites) == 1
    suite = suites[0]
    assert suite.tests == (TestName("a case"),)
    assert (suite.binary, suite.runner) == (Path("/b/unit_tests"), "catch")


def test_cargo_listings_are_read_from_their_output_alone(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    """Each crate's test binaries come from cargo's messages, their tests from their listing.

    Both read the output alone: a message or a test name on the error stream is neither.
    """
    message = RunText(
        '{"reason": "compiler-artifact", "executable": "/t/lifecycle",'
        + ' "profile": {"test": true}, "target": {"name": "lifecycle"}}\n'
    )
    tests = RunText("opens: test\ncloses: test\nbench: benchmark\n")
    noise = RunText(
        '{"reason": "compiler-artifact", "executable": "/t/noise",'
        + ' "profile": {"test": true}, "target": {"name": "noise"}}\n'
    )

    def ran(argv: list[CommandWord], cwd: Path, env: Environment) -> Ran:
        del cwd, env
        if CommandWord("--no-run") in argv:
            return Ran(ExitStatus(0), RunText(f"{noise}{message}"), message)
        return Ran(ExitStatus(0), RunText(f"noise: test\n{tests}"), tests)

    monkeypatch.setattr(check_tests_alone, "find_executable", _tool_at)
    monkeypatch.setattr(check_tests_alone, "capture", ran)
    suites = check_tests_alone.rust_suites(Path("/scratch"))
    assert [suite.tests for suite in suites] == [(TestName("opens"), TestName("closes"))] * 2
    assert [suite.label for suite in suites] == ["rust:lifecycle", "rust/excel:lifecycle"]


def test_a_run_keeps_its_output_apart_from_its_error_stream(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    """A run's text is both streams, its output the standard output alone."""

    def finished(
        argv: list[CommandWord], *, cwd: Path, env: Environment
    ) -> subprocess.CompletedProcess[RunText]:
        del cwd, env
        return subprocess.CompletedProcess(argv, 3, RunText("listed\n"), RunText("told\n"))

    monkeypatch.setattr(check_tests_alone, "run_capture", finished)
    ran = check_tests_alone.capture([CommandWord("/bin/tool")], Path("/"), {})
    assert ran == Ran(ExitStatus(3), RunText("listed\ntold\n"), RunText("listed\n"))
