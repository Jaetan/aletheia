# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
"""The clang-tidy facts gate reads what the tool diagnosed and refuses each broken fact.

``tools/check_clang_tidy_facts.py`` runs the toolchain's clang-tidy over a few
lines when the toolchain's pin or the configuration moves.  Its reading of the
tool's output is held here on canned output, so each refusal is shown on the
defect it is for without starting the tool.
"""

from __future__ import annotations

import subprocess
from dataclasses import dataclass, field
from pathlib import Path
from typing import TYPE_CHECKING

import pytest
from _processes import CommandWord

from tools import check_clang_tidy_facts
from tools.check_clang_tidy_facts import (
    CheckName,
    LineNumber,
    ToolOutput,
    check,
    compiler_errors,
    diagnosed_lines,
    strict_mode_refusals,
)

from aletheia.common_types import ExitStatus, Prose

if TYPE_CHECKING:
    from tools.pin_scope import PinGate

_SOURCE = Path("/scratch/calls.cpp")
_CHECK = CheckName("bugprone-argument-comment")


def test_a_diagnosis_is_read_off_its_line() -> None:
    """A warning or an error carrying the check's tag names its line, a note does not."""
    output = ToolOutput(
        f"{_SOURCE}:4:7: error: argument name 'beta' in comment does not match parameter name"
        + " 'alpha' [bugprone-argument-comment,-warnings-as-errors]\n"
        + f"{_SOURCE}:9:7: warning: argument name 'x' in comment [bugprone-argument-comment]\n"
        + f"{_SOURCE}:1:12: note: 'alpha' declared here\n"
        + f"{_SOURCE}:6:1: warning: something else [readability-other]\n"
        + "/elsewhere/calls.cpp:5:1: warning: elsewhere [bugprone-argument-comment]\n"
    )
    assert diagnosed_lines(output, _SOURCE, _CHECK) == {LineNumber(4), LineNumber(9)}


def test_a_tag_that_only_starts_with_the_check_s_name_is_not_its() -> None:
    """A check named by a longer name is another check."""
    output = ToolOutput(f"{_SOURCE}:4:7: warning: text [bugprone-argument-comment-other]\n")
    assert diagnosed_lines(output, _SOURCE, _CHECK) == set()


def test_strict_mode_as_the_comment_says_raises_nothing() -> None:
    """The misnamed comment diagnosed and the bare call not is the fact."""
    assert not strict_mode_refusals({LineNumber(4)})


def test_a_bare_call_diagnosed_is_refused() -> None:
    """A tool that asks for argument comments contradicts the configuration's comment."""
    assert strict_mode_refusals({LineNumber(3), LineNumber(4)}) == [
        Prose("bugprone-argument-comment.StrictMode diagnoses a call carrying no argument comment")
    ]


def test_a_misnamed_comment_passed_is_refused() -> None:
    """A tool that lets a comment name another parameter contradicts it too."""
    assert strict_mode_refusals(set()) == [
        Prose(
            "bugprone-argument-comment.StrictMode passes a comment naming another parameter"
            + " than its own"
        )
    ]


def test_a_compile_error_is_not_a_diagnosis() -> None:
    """Lines the tool cannot compile are a gate that cannot reach its fact."""
    assert compiler_errors(ToolOutput("x.cpp:1:1: error: unknown type [clang-diagnostic-error]\n"))
    assert not compiler_errors(ToolOutput("x.cpp:4:7: error: a [bugprone-argument-comment]\n"))


def test_without_the_tool_the_gate_cannot_reach_its_facts(
    monkeypatch: pytest.MonkeyPatch, tmp_path: Path
) -> None:
    """No clang-tidy-23 on the search path exits 2 rather than passing."""
    monkeypatch.setenv("PATH", str(tmp_path))
    assert check(tmp_path) == ExitStatus(2)


def _out_of_scope(_gate: PinGate, _root: Path) -> bool:
    """Answer that the branch moved nothing a gate rests on."""
    return False


def _never_checked(_root: Path) -> ExitStatus:
    """Fail the test if the gate reaches for the tool."""
    raise AssertionError


def test_a_branch_moving_nothing_the_facts_rest_on_runs_no_tool(
    monkeypatch: pytest.MonkeyPatch, tmp_path: Path
) -> None:
    """Out of scope, the gate passes without reaching for the tool."""

    def the_tree() -> Path:
        return tmp_path

    monkeypatch.setattr(check_clang_tidy_facts, "git_toplevel", the_tree)
    monkeypatch.setattr(check_clang_tidy_facts, "gate_runs", _out_of_scope)
    monkeypatch.setattr(check_clang_tidy_facts, "check", _never_checked)
    monkeypatch.setattr("sys.argv", ["check_clang_tidy_facts"])
    assert check_clang_tidy_facts.main() == ExitStatus(0)


@dataclass
class _Linter:
    """Answers the gate's run of clang-tidy with what a release of it would print."""

    diagnosed: tuple[LineNumber, ...]
    compiles: bool = True
    asked: list[list[CommandWord]] = field(default_factory=list)
    read: list[Prose] = field(default_factory=list)

    def answer(self, cmd: list[CommandWord]) -> subprocess.CompletedProcess[Prose]:
        """Read the lines the gate wrote and diagnose the chosen ones under the check's tag."""
        self.asked.append(cmd)
        source = Path(cmd[4])
        self.read.append(Prose(source.read_text(encoding="utf-8")))
        printed = [
            f"{source}:{line}:7: error: argument name mismatch [bugprone-argument-comment]"
            for line in self.diagnosed
        ]
        if not self.compiles:
            printed.append(f"{source}:1:1: error: unknown type name [clang-diagnostic-error]")
        return subprocess.CompletedProcess(cmd, 1, Prose("\n".join(printed)), Prose(""))


def _tidy(monkeypatch: pytest.MonkeyPatch, linter: _Linter) -> None:
    """Stand ``linter`` in for the toolchain's clang-tidy."""

    def found(name: CommandWord) -> CommandWord:
        assert name == "clang-tidy-23"
        return CommandWord("/usr/bin/clang-tidy-23")

    monkeypatch.setattr(check_clang_tidy_facts, "find_executable", found)
    monkeypatch.setattr(check_clang_tidy_facts, "run_capture", linter.answer)


def test_the_tool_reads_the_lines_under_the_tree_s_configuration(
    monkeypatch: pytest.MonkeyPatch, tmp_path: Path, capsys: pytest.CaptureFixture[Prose]
) -> None:
    """One check, the tree's configuration, C++23, and the facts' lines where they belong."""
    linter = _Linter((LineNumber(4),))
    _tidy(monkeypatch, linter)
    assert check(tmp_path) == ExitStatus(0)
    assert len(linter.asked) == 1
    cmd = linter.asked[0]
    assert cmd[:4] == [
        "/usr/bin/clang-tidy-23",
        "--quiet",
        f"--config-file={tmp_path / 'cpp' / '.clang-tidy'}",
        "-checks=-*,bugprone-argument-comment",
    ]
    assert Path(cmd[4]).name == "calls.cpp"
    assert cmd[5:] == ["--", "-std=c++23"]
    lines = linter.read[0].splitlines()
    assert lines[0] == "void f(int alpha, int beta);"
    assert lines[2].strip() == "f(1, 2);"
    assert lines[3].strip() == "f(/*beta=*/1, 2);"
    assert capsys.readouterr().out == ""


def test_a_tool_breaking_the_fact_is_refused_by_name(
    monkeypatch: pytest.MonkeyPatch, tmp_path: Path, capsys: pytest.CaptureFixture[Prose]
) -> None:
    """Each broken half is printed under the gate's name."""
    _tidy(monkeypatch, _Linter((LineNumber(3),)))
    assert check(tmp_path) == ExitStatus(1)
    assert capsys.readouterr().out == (
        "check-clang-tidy-facts: bugprone-argument-comment.StrictMode diagnoses a call"
        + " carrying no argument comment\n"
        + "check-clang-tidy-facts: bugprone-argument-comment.StrictMode passes a comment"
        + " naming another parameter than its own\n"
    )


def test_lines_the_tool_cannot_compile_reach_no_fact(
    monkeypatch: pytest.MonkeyPatch, tmp_path: Path, capsys: pytest.CaptureFixture[Prose]
) -> None:
    """A compile error exits 2 with what the tool printed, whatever it diagnosed."""
    _tidy(monkeypatch, _Linter((LineNumber(4),), compiles=False))
    assert check(tmp_path) == ExitStatus(2)
    said = capsys.readouterr().out
    assert said.startswith("check-clang-tidy-facts: clang-tidy-23 could not compile the lines:\n")
    assert "[clang-diagnostic-error]" in said


def test_without_the_tool_the_gate_says_so(
    monkeypatch: pytest.MonkeyPatch, tmp_path: Path, capsys: pytest.CaptureFixture[Prose]
) -> None:
    """The missing binary is named under the gate's name."""
    monkeypatch.setenv("PATH", str(tmp_path))
    assert check(tmp_path) == ExitStatus(2)
    assert capsys.readouterr().out == (
        "check-clang-tidy-facts: required executable not found on PATH: clang-tidy-23\n"
    )


def test_in_scope_the_gate_s_verdict_is_the_check_s(
    monkeypatch: pytest.MonkeyPatch, tmp_path: Path
) -> None:
    """A branch moving what the facts rest on gets the check's own exit status."""

    def the_tree() -> Path:
        return tmp_path

    def in_scope(_gate: PinGate, _root: Path) -> bool:
        return True

    def refusing(root: Path) -> ExitStatus:
        assert root == tmp_path
        return ExitStatus(1)

    monkeypatch.setattr(check_clang_tidy_facts, "git_toplevel", the_tree)
    monkeypatch.setattr(check_clang_tidy_facts, "gate_runs", in_scope)
    monkeypatch.setattr(check_clang_tidy_facts, "check", refusing)
    monkeypatch.setattr("sys.argv", ["check_clang_tidy_facts"])
    assert check_clang_tidy_facts.main() == ExitStatus(1)


def test_the_gate_refuses_an_argument_it_does_not_take(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    """An argument the gate does not take stops it before it reads anything."""
    monkeypatch.setattr("sys.argv", ["check_clang_tidy_facts", "--unknown"])
    with pytest.raises(SystemExit) as stopped:
        _ = check_clang_tidy_facts.main()
    assert stopped.value.code == 2
