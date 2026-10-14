# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
"""The JSON cleanup gate reads its program's ending as the fact, a refusal, or no answer.

``tools/check_json_cleanup_abort.py`` builds ``cpp/tests/json_cleanup_abort.cpp``
in the C++ test tree and runs it when the JSON library's release moves.  The
build and the run are replaced here by answers the test writes, so how each
ending is read is held without a compiler.
"""

from __future__ import annotations

import subprocess
from typing import TYPE_CHECKING

import pytest
from _processes import CommandWord

from tools import check_json_cleanup_abort
from tools.check_json_cleanup_abort import TARGET, check

from aletheia.common_types import ExitStatus, Prose

if TYPE_CHECKING:
    from pathlib import Path

    from tools.pin_scope import PinGate


def _configured(tmp_path: Path) -> Path:
    """Return a repository root whose C++ test tree reads as configured."""
    tree = tmp_path / "cpp" / "build"
    tree.mkdir(parents=True)
    _ = (tree / "CMakeCache.txt").write_text("", encoding="utf-8")
    return tmp_path


def _answers(
    monkeypatch: pytest.MonkeyPatch, *, built: ExitStatus, ran: ExitStatus
) -> list[list[CommandWord]]:
    """Answer the build with ``built`` and the program with ``ran``; return what was run."""
    asked: list[list[CommandWord]] = []

    def answer(cmd: list[CommandWord]) -> subprocess.CompletedProcess[Prose]:
        asked.append(cmd)
        status = built if cmd[1:2] == ["--build"] else ran
        return subprocess.CompletedProcess(cmd, status, Prose("out "), Prose("said\n"))

    def cmake(name: CommandWord) -> CommandWord:
        assert name == "cmake"
        return CommandWord("/usr/bin/cmake")

    monkeypatch.setattr(check_json_cleanup_abort, "run_capture", answer)
    monkeypatch.setattr(check_json_cleanup_abort, "find_executable", cmake)
    return asked


@pytest.mark.parametrize(
    ("ending", "verdict"),
    [
        (ExitStatus(0), ExitStatus(0)),
        (ExitStatus(1), ExitStatus(1)),
        (ExitStatus(134), ExitStatus(2)),
    ],
)
def test_the_program_s_ending_is_the_verdict(
    monkeypatch: pytest.MonkeyPatch,
    tmp_path: Path,
    capsys: pytest.CaptureFixture[Prose],
    ending: ExitStatus,
    verdict: ExitStatus,
) -> None:
    """Only the terminate handler's 0 passes, 1 refuses, and any other end is no answer."""
    root = _configured(tmp_path)
    asked = _answers(monkeypatch, built=ExitStatus(0), ran=ending)
    tree = root / "cpp" / "build"
    assert check(root) == verdict
    assert asked[0][:6] == ["/usr/bin/cmake", "--build", str(tree), "--target", TARGET, "-j"]
    assert int(asked[0][6]) >= 1
    assert asked[1:] == [[str(tree / TARGET)]]
    said = capsys.readouterr().out
    if ending == 0:
        assert said == ""
    else:
        assert said == f"check-json-cleanup-abort: json_cleanup_abort exited {ending}: out said\n"


def test_a_program_that_does_not_build_is_no_answer(
    monkeypatch: pytest.MonkeyPatch, tmp_path: Path, capsys: pytest.CaptureFixture[Prose]
) -> None:
    """A build that fails reaches no fact, and nothing is run."""
    asked = _answers(monkeypatch, built=ExitStatus(2), ran=ExitStatus(0))
    assert check(_configured(tmp_path)) == ExitStatus(2)
    assert len(asked) == 1
    assert capsys.readouterr().out == (
        "check-json-cleanup-abort: json_cleanup_abort does not build:\nout said\n\n"
    )


def test_an_unconfigured_tree_is_no_answer(
    monkeypatch: pytest.MonkeyPatch, tmp_path: Path, capsys: pytest.CaptureFixture[Prose]
) -> None:
    """With no test tree to build in, the gate exits 2 and builds nothing."""
    asked = _answers(monkeypatch, built=ExitStatus(0), ran=ExitStatus(0))
    assert check(tmp_path) == ExitStatus(2)
    assert not asked
    assert capsys.readouterr().out == (
        f"check-json-cleanup-abort: {tmp_path / 'cpp' / 'build'} is not configured;"
        + " the C++ lane configures it\n"
    )


def _out_of_scope(_gate: PinGate, _root: Path) -> bool:
    """Answer that the branch moved nothing a gate rests on."""
    return False


def _never_checked(_root: Path) -> ExitStatus:
    """Fail the test if the gate reaches for the program."""
    raise AssertionError


def test_a_branch_moving_nothing_the_fact_rests_on_builds_nothing(
    monkeypatch: pytest.MonkeyPatch, tmp_path: Path
) -> None:
    """Out of scope, the gate passes without building."""

    def the_tree() -> Path:
        return tmp_path

    monkeypatch.setattr(check_json_cleanup_abort, "git_toplevel", the_tree)
    monkeypatch.setattr(check_json_cleanup_abort, "gate_runs", _out_of_scope)
    monkeypatch.setattr(check_json_cleanup_abort, "check", _never_checked)
    monkeypatch.setattr("sys.argv", ["check_json_cleanup_abort"])
    assert check_json_cleanup_abort.main() == ExitStatus(0)


def test_in_scope_the_gate_s_verdict_is_the_check_s(
    monkeypatch: pytest.MonkeyPatch, tmp_path: Path
) -> None:
    """A branch moving what the fact rests on gets the check's own exit status."""

    def the_tree() -> Path:
        return tmp_path

    def in_scope(_gate: PinGate, _root: Path) -> bool:
        return True

    def refusing(root: Path) -> ExitStatus:
        assert root == tmp_path
        return ExitStatus(1)

    monkeypatch.setattr(check_json_cleanup_abort, "git_toplevel", the_tree)
    monkeypatch.setattr(check_json_cleanup_abort, "gate_runs", in_scope)
    monkeypatch.setattr(check_json_cleanup_abort, "check", refusing)
    monkeypatch.setattr("sys.argv", ["check_json_cleanup_abort"])
    assert check_json_cleanup_abort.main() == ExitStatus(1)


def test_the_gate_refuses_an_argument_it_does_not_take(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    """An argument the gate does not take stops it before it reads anything."""
    monkeypatch.setattr("sys.argv", ["check_json_cleanup_abort", "--unknown"])
    with pytest.raises(SystemExit) as stopped:
        _ = check_json_cleanup_abort.main()
    assert stopped.value.code == 2
