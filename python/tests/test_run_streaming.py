# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
"""Tests for ``tools._common.run_streaming``.

The helper exists because a captured child takes its whole log with it when a
wall clock kills it, so the properties under test are the ones a kill depends
on: every line reaches the sink *as it is produced*, the sink sees the same
text the return value carries, and stderr is in that stream rather than beside
it.  What only a pipe between two processes shows -- line framing, the merge
of the child's two streams, a line delivered while the child still runs -- is
driven through a real child that proves ordering without waiting on physical
time: it blocks until the sink has seen its first line, so a buffered
implementation deadlocks instead of passing.  The helper's own bookkeeping --
the environment it builds, the text and status it returns, its sink's failure
report -- is driven through a stand-in child that hands back fixed output.
"""

from __future__ import annotations

import errno
import io
import os
import subprocess
import sys
from dataclasses import dataclass, field
from typing import TYPE_CHECKING, Literal, NewType, Self

import pytest

from tools._common import run_streaming

from aletheia.common_types import ExitStatus, Prose

if TYPE_CHECKING:
    from collections.abc import Sequence
    from pathlib import Path
    from types import TracebackType

    from _processes import CommandWord

# The name of an environment variable, and the value it holds.
VariableName = NewType("VariableName", str)
VariableValue = NewType("VariableValue", str)
type Environment = dict[VariableName, VariableValue]


def _python_child(*statements: str) -> list[str]:
    """Build a child running ``statements``, addressed by the absolute interpreter path."""
    return [sys.executable, "-c", "\n".join(statements)]


# What a stand-in child is started as: a child that would fail loudly if it ever ran.
_STAND_IN = _python_child("raise SystemExit('a stand-in child never runs')")

# How run_streaming opens a child's pipe: stdout piped, stderr merged into it,
# text mode, line buffered.
_PIPE = {"stdout": subprocess.PIPE, "stderr": subprocess.STDOUT, "text": True, "bufsize": 1}
type PipeOption = Literal[-1, -2, 1] | bool

# The status of a child that succeeded.
_SUCCESS = ExitStatus(0)


class _Child:
    """A started child that has written ``output`` to its merged pipe and ends with ``status``."""

    def __init__(self, output: Prose, status: ExitStatus) -> None:
        self.stdout = io.StringIO(output)
        self._status = status

    def __enter__(self) -> Self:
        return self

    def __exit__(
        self,
        exc_type: type[BaseException] | None,
        exc: BaseException | None,
        traceback: TracebackType | None,
    ) -> None:
        """Leave the child as it is: it has nothing left to reap."""

    def wait(self) -> ExitStatus:
        """Return the status the child ends with."""
        return self._status


@dataclass
class _Spawns:
    """A stand-in for ``subprocess.Popen`` that starts no process.

    It records the environment each child is given, checks the pipe the helper
    asks for, and hands back a child that has written ``output``.
    """

    output: Prose
    status: ExitStatus = _SUCCESS
    envs: list[Environment] = field(default_factory=list[Environment])

    def __call__(
        self,
        cmd: Sequence[CommandWord],
        *,
        cwd: Path | None,
        env: Environment,
        **pipe: PipeOption,
    ) -> _Child:
        """Record ``env`` and return the child, refusing a pipe set up any other way."""
        assert cmd == _STAND_IN, cmd
        assert cwd is None, cwd
        assert pipe == _PIPE, pipe
        self.envs.append(env)
        return _Child(self.output, self.status)


def _stand_in(
    monkeypatch: pytest.MonkeyPatch, output: Prose, status: ExitStatus = _SUCCESS
) -> _Spawns:
    """Start every child of the rest of the test as a stand-in that wrote ``output``."""
    spawns = _Spawns(output, status)
    monkeypatch.setattr(subprocess, "Popen", spawns)
    return spawns


@pytest.mark.process(
    "each line is framed by the text-mode pipe of a real child, which no fake stdout holds"
)
def test_every_line_reaches_the_sink_in_order() -> None:
    """The sink is called once per line, in order, newline included."""
    seen: list[str] = []
    proc = run_streaming(
        _python_child("for i in range(3): print(f'line {i}')"),
        sink=seen.append,
    )
    assert seen == ["line 0\n", "line 1\n", "line 2\n"]
    assert proc.returncode == 0


def test_the_return_value_is_the_joined_sink_text(monkeypatch: pytest.MonkeyPatch) -> None:
    """What the caller parses is exactly what the sink was shown."""
    output = Prose("row 0\nrow 1\nrow 2\nrow 3\n")
    _ = _stand_in(monkeypatch, output)
    seen: list[str] = []
    proc = run_streaming(_STAND_IN, sink=seen.append)
    assert seen == ["row 0\n", "row 1\n", "row 2\n", "row 3\n"]
    assert proc.stdout == "".join(seen) == output
    assert proc.stderr == ""


@pytest.mark.process(
    "the order across a child's two streams is set by the one pipe it is given for both"
)
def test_stderr_is_merged_into_the_stream() -> None:
    """A diagnostic and the progress line before it stay legible in one stream."""
    seen: list[str] = []
    proc = run_streaming(
        _python_child(
            "import sys",
            "print('progress')",
            "sys.stdout.flush()",
            "print('diagnostic', file=sys.stderr)",
        ),
        sink=seen.append,
    )
    assert seen == ["progress\n", "diagnostic\n"]
    assert proc.stdout == "progress\ndiagnostic\n"


@pytest.mark.process(
    "a line reaching the sink before the child exits is a property of a live child's pipe"
)
def test_a_line_arrives_before_the_child_exits(tmp_path: Path) -> None:
    """The defining property: output is observable while the child still runs.

    The child writes its first line, then blocks reading a FIFO that the sink
    writes to once it has seen that line, and only then writes its second.  An
    implementation that holds output until exit never calls the sink while the
    child runs, so the child never gets past its read and the run hangs, the
    test run's own limit reporting it, rather than passes.
    """
    handshake = tmp_path / "sink-saw-it"
    os.mkfifo(handshake)
    seen: list[str] = []

    def sink(line: str) -> None:
        seen.append(line)
        if line.startswith("first"):
            with handshake.open("w", encoding="utf-8") as answer:
                _ = answer.write("seen\n")

    proc = run_streaming(
        _python_child(
            "import sys",
            "print('first')",
            "sys.stdout.flush()",
            f"answer = open({str(handshake)!r}, encoding='utf-8').read()",
            "print('second' if answer == 'seen\\n' else 'no answer')",
        ),
        sink=sink,
    )
    assert proc.returncode == 0
    assert seen == ["first\n", "second\n"]


def test_the_exit_code_is_the_child_s(monkeypatch: pytest.MonkeyPatch) -> None:
    """A failing child is reported as failing, not swallowed by the streaming."""
    _ = _stand_in(monkeypatch, Prose("bye\n"), ExitStatus(3))
    proc = run_streaming(_STAND_IN, sink=lambda _: None)
    assert proc.returncode == 3
    assert proc.stdout == "bye\n"


def test_a_python_child_is_unbuffered_without_asking(monkeypatch: pytest.MonkeyPatch) -> None:
    """A Python child block-buffers a pipe; the helper sets PYTHONUNBUFFERED itself."""
    spawns = _stand_in(monkeypatch, Prose(""))
    _ = run_streaming(_STAND_IN, sink=lambda _: None)
    assert spawns.envs == [dict(os.environ) | {"PYTHONUNBUFFERED": "1"}]


def test_a_caller_env_is_extended_not_replaced_for_the_buffering_flag(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    """A custom env still reaches the child, with the buffering flag added to it."""
    spawns = _stand_in(monkeypatch, Prose(""))
    caller = {"ALETHEIA_PROBE": "set-by-caller", "PATH": "/usr/bin:/bin"}
    _ = run_streaming(_STAND_IN, env=caller, sink=lambda _: None)
    assert spawns.envs == [caller | {"PYTHONUNBUFFERED": "1"}]
    assert caller == {"ALETHEIA_PROBE": "set-by-caller", "PATH": "/usr/bin:/bin"}


@pytest.mark.parametrize("output", [Prose("only line\n"), Prose("")])
def test_no_trailing_empty_line_is_invented(monkeypatch: pytest.MonkeyPatch, output: Prose) -> None:
    """An empty stream yields no sink calls; a one-line stream yields exactly one."""
    _ = _stand_in(monkeypatch, output)
    seen: list[str] = []
    _ = run_streaming(_STAND_IN, sink=seen.append)
    assert seen == ([] if not output else ["only line\n"])


class _FailingStderr:
    """A stderr whose write fails the way a filesystem with no space left fails it."""

    def __init__(self, fd: int | None) -> None:
        self._fd = fd

    def write(self, _line: str) -> int:
        """Fail as the real stream does when the filesystem behind it is full."""
        raise OSError(errno.ENOSPC, "No space left on device")

    def flush(self) -> None:
        """Never reached, the write failing first."""

    def fileno(self) -> int:
        """Return the descriptor the space is measured through, or refuse to have one."""
        if self._fd is None:
            refusal = "fileno"
            raise io.UnsupportedOperation(refusal)
        return self._fd


def test_a_write_failure_is_reported_with_the_space_left_on_the_filesystem(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    """The default sink names what stderr writes to and what is left of it.

    The failure this carries is a full temp filesystem, where the traceback on
    its own names the progress line that happened to be writing and nothing
    about the disk.
    """
    _ = _stand_in(monkeypatch, Prose("progress\n"))
    target = tmp_path / "progress.log"
    with target.open("w", encoding="utf-8") as handle:
        monkeypatch.setattr(sys, "stderr", _FailingStderr(handle.fileno()))
        with pytest.raises(RuntimeError) as failure:
            _ = run_streaming(_STAND_IN)
    reported = str(failure.value)
    assert "No space left on device" in reported
    assert str(target) in reported
    assert "bytes free" in reported


def test_a_stderr_with_no_descriptor_reports_the_failure_as_unmeasured(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    """A stream the space cannot be read through still reports the write failure."""
    _ = _stand_in(monkeypatch, Prose("progress\n"))
    monkeypatch.setattr(sys, "stderr", _FailingStderr(None))
    with pytest.raises(RuntimeError) as failure:
        _ = run_streaming(_STAND_IN)
    reported = str(failure.value)
    assert "No space left on device" in reported
    assert "unknown" in reported
