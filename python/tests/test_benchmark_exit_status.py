# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
"""The Python harnesses' exit status when stdout refuses the report, as their process ends.

The interpreter flushes stdout as it exits, and a flush that fails there turns
the status into 120 and writes a warning to stderr, which only a process of its
own shows.  Each harness runs as the runners start it, ``python -m
benchmarks.<name>`` from ``python/``, against the built kernel at its smallest
counts, with stdout opened on ``/dev/full`` and stderr on a file of the test's
own, both written by the child itself.  The throughput benchmark exits 1 and the
stability harness 2, each with the line naming the write as the whole of its
stderr.
"""

from __future__ import annotations

import os
import subprocess
import sys
from pathlib import Path
from typing import TYPE_CHECKING, Final, NamedTuple

import pytest
from _cli_check_helpers import FFI_LIB, skip_without_ffi
from _full_stdout import NO_SPACE
from _processes import CommandWord

from aletheia.common_types import ExitStatus, PositiveInt, Prose

if TYPE_CHECKING:
    from collections.abc import Mapping

    from benchmarks.stability import CountVariable

_PYTHON_DIR: Final = Path(__file__).resolve().parents[1]
_EXIT_STATUS: Final = "the claim is the program's exit status, which only a process of its own has"


class HarnessRun(NamedTuple):
    """How a harness's process ended: its exit status and its stderr."""

    returncode: ExitStatus
    stderr: Prose


def _run_on_full_stdout(
    tmp_path: Path, words: list[CommandWord], counts: Mapping[CountVariable, PositiveInt]
) -> HarnessRun:
    """Run ``python -m`` on ``words`` against the built kernel, stdout on ``/dev/full``.

    ``counts`` are set in the child's environment beside this process's, and
    stderr goes to a file under ``tmp_path``, read back once the child has exited.
    """
    stderr_path = tmp_path / "stderr"
    with Path("/dev/full").open("wb") as stdout, stderr_path.open("wb") as stderr:
        done = subprocess.run(
            [sys.executable, "-m", *words],
            cwd=_PYTHON_DIR,
            env=os.environ
            | {"ALETHEIA_LIB": str(FFI_LIB)}
            | {name: str(count) for name, count in counts.items()},
            stdout=stdout,
            stderr=stderr,
            check=False,
        )
    return HarnessRun(ExitStatus(done.returncode), Prose(stderr_path.read_text(encoding="utf-8")))


@pytest.mark.process(_EXIT_STATUS)
def test_a_throughput_report_stdout_refuses_exits_1(tmp_path: Path) -> None:
    """The run exits 1, not the interpreter's 120, with its line as the whole of stderr."""
    skip_without_ffi()
    words = ("benchmarks.throughput", "--frames", "1", "--runs", "1", "--warmup", "0")
    run = _run_on_full_stdout(tmp_path, [CommandWord(w) for w in words], {})
    line = f"benchmark: writing the throughput report failed: {NO_SPACE}\n"
    assert run == HarnessRun(ExitStatus(1), Prose(line))


@pytest.mark.process(_EXIT_STATUS)
def test_a_stability_report_stdout_refuses_exits_2(tmp_path: Path) -> None:
    """The run exits 2, a run without a verdict, with its line as the whole of stderr."""
    skip_without_ffi()
    counts: dict[CountVariable, PositiveInt] = {
        "ALETHEIA_STABILITY_CYCLES": 1,
        "ALETHEIA_STABILITY_FRAMES": 1,
    }
    run = _run_on_full_stdout(tmp_path, [CommandWord("benchmarks.stability")], counts)
    line = f"stability: writing the report failed: {NO_SPACE}\n"
    assert run == HarnessRun(ExitStatus(2), Prose(line))
