# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
"""Tests for ``tools._common.run_streaming``.

The helper exists because a captured child takes its whole log with it when a
wall clock kills it, so the properties under test are the ones a kill depends
on: every line reaches the sink *as it is produced*, the sink sees the same
text the return value carries, and stderr is in that stream rather than beside
it.  The guards inject a recording sink and drive a child that proves ordering
without waiting on physical time -- the child blocks until the sink has seen
its first line, so a buffered implementation deadlocks instead of passing.
"""

from __future__ import annotations

import sys
from typing import TYPE_CHECKING

import pytest

from tools._common import run_streaming

if TYPE_CHECKING:
    from pathlib import Path


def _python_child(*statements: str) -> list[str]:
    """Build a child running ``statements``, addressed by the absolute interpreter path."""
    return [sys.executable, "-c", "\n".join(statements)]


def test_every_line_reaches_the_sink_in_order() -> None:
    """The sink is called once per line, in order, newline included."""
    seen: list[str] = []
    proc = run_streaming(
        _python_child("for i in range(3): print(f'line {i}')"),
        sink=seen.append,
    )
    assert seen == ["line 0\n", "line 1\n", "line 2\n"]
    assert proc.returncode == 0


def test_the_return_value_is_the_joined_sink_text() -> None:
    """What the caller parses is exactly what the sink was shown."""
    seen: list[str] = []
    proc = run_streaming(
        _python_child("for i in range(4): print(f'row {i}')"),
        sink=seen.append,
    )
    assert proc.stdout == "".join(seen)
    assert proc.stderr == ""


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


def test_a_line_arrives_before_the_child_exits(tmp_path: Path) -> None:
    """The defining property: output is observable while the child still runs.

    The child writes its first line, then waits for the sink to answer by
    creating a file.  An implementation that holds output until exit cannot
    answer while the child runs, so the child reaches its own deadline and
    reports that by exiting non-zero with a different last line -- the failure
    this asserts.  A correct implementation answers in milliseconds and never
    approaches the deadline, so the wait is paid only by a broken one.
    """
    handshake = tmp_path / "sink-saw-it"
    seen: list[str] = []

    def sink(line: str) -> None:
        seen.append(line)
        if line.startswith("first"):
            handshake.write_text("seen")

    proc = run_streaming(
        _python_child(
            "import sys, time",
            "print('first')",
            "sys.stdout.flush()",
            f"path = {str(handshake)!r}",
            "import os",
            "deadline = time.monotonic() + 20",
            "while not os.path.exists(path) and time.monotonic() < deadline:",
            "    time.sleep(0.01)",
            "if not os.path.exists(path):",
            "    print('NO-HANDSHAKE')",
            "    sys.exit(7)",
            "print('second')",
        ),
        sink=sink,
    )
    assert proc.returncode == 0, "the child never saw the sink answer while it was alive"
    assert seen == ["first\n", "second\n"]


def test_the_exit_code_is_the_child_s() -> None:
    """A failing child is reported as failing, not swallowed by the streaming."""
    child = _python_child("import sys", "print('bye')", "sys.exit(3)")
    proc = run_streaming(child, sink=lambda _: None)
    assert proc.returncode == 3
    assert proc.stdout == "bye\n"


def test_a_python_child_is_unbuffered_without_asking() -> None:
    """A Python child block-buffers a pipe; the helper sets PYTHONUNBUFFERED itself."""
    seen: list[str] = []
    proc = run_streaming(
        _python_child("import os", "print(os.environ.get('PYTHONUNBUFFERED', 'unset'))"),
        sink=seen.append,
    )
    assert seen == ["1\n"]
    assert proc.returncode == 0


def test_a_caller_env_is_extended_not_replaced_for_the_buffering_flag() -> None:
    """A custom env still reaches the child, with the buffering flag added to it."""
    seen: list[str] = []
    proc = run_streaming(
        _python_child(
            "import os",
            "print(os.environ.get('ALETHEIA_PROBE', 'unset'))",
            "print(os.environ.get('PYTHONUNBUFFERED', 'unset'))",
        ),
        env={"ALETHEIA_PROBE": "set-by-caller", "PATH": "/usr/bin:/bin"},
        sink=seen.append,
    )
    assert seen == ["set-by-caller\n", "1\n"]
    assert proc.returncode == 0


@pytest.mark.parametrize("statements", [("print('only line')",), ("pass",)])
def test_no_trailing_empty_line_is_invented(statements: tuple[str, ...]) -> None:
    """An empty stream yields no sink calls; a one-line stream yields exactly one."""
    seen: list[str] = []
    _ = run_streaming(_python_child(*statements), sink=seen.append)
    assert seen == ([] if statements == ("pass",) else ["only line\n"])
