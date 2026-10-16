# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
"""Tests for ``tools.stability_run``'s Go lane: how it reads the Go harness's exit status.

A harness's exit 0 or 1 is a verdict read from its report, and any other exit
is a run with no verdict, whose stderr the summary quotes.  ``go run`` reports
a program's non-zero exit as its own exit 1, so the lane builds the harness and
runs the binary, built outside the artifact directory CI uploads and removed
after the run, and a build that fails is a run with no verdict too.  The go
tool and the harness it builds are answered by a stand-in, so no test starts a
process.
"""

from __future__ import annotations

import subprocess
from pathlib import Path
from typing import TYPE_CHECKING, NamedTuple, TypedDict, Unpack

import pytest
from _processes import CommandWord

from tools import stability_run
from tools.stability_run import STDERR_SNIPPET_LEN, Run, run_go

from aletheia.common_types import ExitStatus, Prose

if TYPE_CHECKING:
    from collections.abc import Mapping

_GO = CommandWord("/opt/go/bin/go")
_PACKAGE = CommandWord("./benchmarks/stability/")
_ENV = {"ALETHEIA_LIB": "/repo/build/libaletheia-ffi.so"}


class _Answer(NamedTuple):
    """What a process answers: its exit status and what it wrote."""

    status: ExitStatus
    stdout: Prose
    stderr: Prose


class _Lane(NamedTuple):
    """What the Go lane did: its run, the commands it started and the binary it built."""

    run: Run
    asked: list[list[CommandWord]]
    binary: Path


class _Verdict(NamedTuple):
    """A harness's exit status with a verdict, the report it writes and that verdict."""

    status: ExitStatus
    report: Prose
    passed: bool


class _RunOptions(TypedDict):
    """The keywords the runner passes ``subprocess.run`` with a command."""

    cwd: Path
    env: Mapping[Prose, Prose]
    capture_output: bool
    text: bool
    check: bool


_BUILT = _Answer(ExitStatus(0), Prose(""), Prose(""))
_PASSED = _Answer(ExitStatus(0), Prose('{"passed": true}\n'), Prose(""))


def _run_go(
    monkeypatch: pytest.MonkeyPatch, artifact_dir: Path, *, build: _Answer, harness: _Answer
) -> _Lane:
    """Run the Go lane into ``artifact_dir`` against a stand-in go tool; return what it did.

    ``go build -o <binary>`` answers ``build``, writing the binary when it
    succeeds, and the binary it names answers ``harness``.
    """
    built: list[Path] = []
    asked: list[list[CommandWord]] = []

    def go(
        cmd: list[CommandWord], **options: Unpack[_RunOptions]
    ) -> subprocess.CompletedProcess[Prose]:
        """Record ``cmd`` and answer it as the go tool or the built harness would."""
        assert options == {
            "cwd": stability_run.REPO_ROOT / "go",
            "env": _ENV,
            "capture_output": True,
            "text": True,
            "check": False,
        }
        asked.append(cmd)
        match cmd:
            case [tool, "build", "-o", binary, package] if (tool, package) == (_GO, _PACKAGE):
                built.append(Path(binary))
                if build.status == 0:
                    Path(binary).write_bytes(b"")
                answer = build
            case [program] if Path(program) in built:
                answer = harness
            case _:
                pytest.fail(f"a command neither the go tool nor a built harness answers: {cmd}")
        return subprocess.CompletedProcess(cmd, answer.status, answer.stdout, answer.stderr)

    def which(name: Prose) -> CommandWord:
        """Answer the stand-in go tool's path for ``go``."""
        assert name == "go"
        return _GO

    monkeypatch.setattr("tools.stability_run.find_executable", which)
    monkeypatch.setattr("tools.stability_run.subprocess.run", go)
    run = run_go(artifact_dir, _ENV)
    assert len(built) == 1
    return _Lane(run, asked, built[0])


def _built_and_ran(binary: Path) -> list[list[CommandWord]]:
    """Return the commands of a lane that built the harness as ``binary`` and ran it."""
    program = CommandWord(str(binary))
    return [[_GO, CommandWord("build"), CommandWord("-o"), program, _PACKAGE], [program]]


def test_the_go_harness_is_built_outside_the_artifacts_and_removed(
    monkeypatch: pytest.MonkeyPatch, tmp_path: Path
) -> None:
    """The binary is built in a directory of its own, gone after the run; only the report stays."""
    lane = _run_go(monkeypatch, tmp_path, build=_BUILT, harness=_PASSED)
    assert not lane.binary.is_relative_to(tmp_path)
    assert not lane.binary.parent.exists()
    assert [path.name for path in tmp_path.iterdir()] == ["go.json"]


def test_a_go_harness_with_no_verdict_is_quoted(
    monkeypatch: pytest.MonkeyPatch, tmp_path: Path
) -> None:
    """A harness that exits 2 is a run with no verdict, whose stderr the run quotes."""
    stderr = Prose("stability: the opening snapshot failed: /proc/self/fd is gone\n")
    harness = _Answer(ExitStatus(2), Prose(""), stderr)
    lane = _run_go(monkeypatch, tmp_path, build=_BUILT, harness=harness)
    error = "go harness exited 2: stability: the opening snapshot failed: /proc/self/fd is gone"
    assert lane.run == Run("go", tmp_path / "go.json", passed=False, error=error)
    assert lane.asked == _built_and_ran(lane.binary)


@pytest.mark.parametrize(
    "verdict",
    [
        _Verdict(ExitStatus(0), Prose('{"passed": true}\n'), passed=True),
        _Verdict(ExitStatus(1), Prose('{"passed": false}\n'), passed=False),
    ],
    ids=["passed", "failed"],
)
def test_a_go_verdict_is_read_from_the_report(
    monkeypatch: pytest.MonkeyPatch, tmp_path: Path, verdict: _Verdict
) -> None:
    """A harness that exits 0 or 1 is a verdict, read from the report it archives."""
    harness = _Answer(verdict.status, verdict.report, Prose(""))
    lane = _run_go(monkeypatch, tmp_path, build=_BUILT, harness=harness)
    assert lane.run == Run("go", tmp_path / "go.json", passed=verdict.passed)
    assert (tmp_path / "go.json").read_text(encoding="utf-8") == verdict.report
    assert lane.asked == _built_and_ran(lane.binary)


_SYNTAX_ERROR = "benchmarks/stability/main.go:3:1: syntax error: non-declaration statement"
_TOO_MANY = (
    "# github.com/Jaetan/aletheia/go/v5/benchmarks/stability\n"
    + "".join(f"benchmarks/stability/main.go:{line}:1: undefined: frame\n" for line in range(3, 13))
    + "benchmarks/stability/main.go:13:1: too many errors\n"
)


@pytest.mark.parametrize(
    ("stderr", "quoted"),
    [
        (Prose(f"{_SYNTAX_ERROR}\n"), Prose(_SYNTAX_ERROR)),
        (Prose(_TOO_MANY), Prose(_TOO_MANY[:STDERR_SNIPPET_LEN])),
    ],
    ids=["one error", "past the cap"],
)
def test_a_go_harness_that_does_not_build_has_no_verdict(
    monkeypatch: pytest.MonkeyPatch, tmp_path: Path, stderr: Prose, quoted: Prose
) -> None:
    """A failed build is a run with no verdict quoting the build's stderr, and nothing runs."""
    build = _Answer(ExitStatus(1), Prose(""), stderr)
    lane = _run_go(monkeypatch, tmp_path, build=build, harness=_PASSED)
    error = f"go harness build exited 1: {quoted}"
    assert lane.run == Run("go", tmp_path / "go.json", passed=False, error=error)
    assert lane.asked == _built_and_ran(lane.binary)[:1]
    assert not lane.binary.parent.exists()
