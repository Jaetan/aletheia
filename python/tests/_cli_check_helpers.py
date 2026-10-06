# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
"""Shared scaffolding for the hermetic ``aletheia check`` CLI regression tests.

Each such test generates its own fixtures in ``tmp_path`` and drives ``aletheia
check`` against the real ``build/libaletheia-ffi.so`` through the CLI's own
``main``, in this process, as the command runs it: the claims are about what
the command answers, which needs no process of its own.  The one exception is a
claim about a runtime that has not yet started: the GHC runtime is
process-global and starts once, so that test runs the command as a fresh
process.  This module centralises both, the FFI-missing skip and the failure
report, so the test files carry only their own fixtures and assertions.
"""

from __future__ import annotations

import contextlib
import io
import os
import subprocess
import sys
from pathlib import Path
from typing import NamedTuple, NewType

import pytest

from aletheia import cli
from aletheia.common_types import ExitStatus, Prose

REPO_ROOT = Path(__file__).resolve().parents[2]
FFI_LIB = REPO_ROOT / "build" / "libaletheia-ffi.so"
_SUBPROCESS_CWD = REPO_ROOT / "python"

# One word of a command line.
CommandWord = NewType("CommandWord", str)


class CheckInputs(NamedTuple):
    """What ``aletheia check`` reads: a log, and a DBC with its checks or one workbook."""

    log: Path
    dbc: Path | None = None
    checks: Path | None = None
    workbook: Path | None = None

    def words(self) -> list[CommandWord]:
        """Return the command line that follows ``aletheia check``."""
        flags = (("--dbc", self.dbc), ("--checks", self.checks), ("--excel", self.workbook))
        named = [
            CommandWord(word)
            for flag, path in flags
            if path is not None
            for word in (flag, str(path))
        ]
        return [*named, CommandWord(str(self.log))]


class CliRun(NamedTuple):
    """How a run of the command ended: its exit status and what it wrote."""

    returncode: ExitStatus
    stdout: Prose
    stderr: Prose


def skip_without_ffi() -> None:
    """Skip the calling test if the FFI shared library has not been built."""
    if not FFI_LIB.exists():
        pytest.skip(f"libaletheia-ffi.so missing at {FFI_LIB} — run 'cabal run shake -- build'")


def run_captured(
    argv: list[str], env: dict[str, str], *, cwd: Path
) -> subprocess.CompletedProcess[str]:
    """Run ``argv`` as a captured-output text subprocess (the shared CLI-drive primitive).

    The single ``subprocess.run`` invocation the CLI regression harnesses share,
    so no test file re-spells the capture/text/no-raise options.  No timeout: a
    test waits on no duration, and a hang is the test run's own limit to report.
    """
    return subprocess.run(argv, cwd=cwd, env=env, capture_output=True, text=True, check=False)


def run_check(inputs: CheckInputs, monkeypatch: pytest.MonkeyPatch) -> CliRun:
    """Run ``aletheia check`` over ``inputs`` in this process against the real ``.so``."""
    monkeypatch.setenv("ALETHEIA_LIB", str(FFI_LIB))
    out, err = io.StringIO(), io.StringIO()
    with contextlib.redirect_stdout(out), contextlib.redirect_stderr(err):
        status = cli.main(["check", *inputs.words()])
    return CliRun(ExitStatus(status), Prose(out.getvalue()), Prose(err.getvalue()))


def run_check_in_a_fresh_process(inputs: CheckInputs) -> CliRun:
    """Run ``aletheia check`` over ``inputs`` as a process of its own, its runtime down."""
    env = dict(os.environ)
    env["ALETHEIA_LIB"] = str(FFI_LIB)
    done = run_captured(
        [sys.executable, "-m", "aletheia", "check", *inputs.words()], env, cwd=_SUBPROCESS_CWD
    )
    return CliRun(ExitStatus(done.returncode), Prose(done.stdout), Prose(done.stderr))


def report(result: CliRun) -> Prose:
    """Render a finished run as a human-readable assertion message."""
    return Prose(
        f"exit={result.returncode}\n"
        + f"--- stdout ---\n{result.stdout}\n"
        + f"--- stderr ---\n{result.stderr}"
    )


def dbc_text(msg_id: int, msg_name: str, signal: str) -> str:
    """Minimal single-message DBC text: standard preamble + one ``BO_`` / ``SG_``.

    ``signal`` is the ``SG_`` body up to (not including) the trailing receiver,
    e.g. ``'VehicleSpeed : 0|16@1+ (0.01,0) [0|655.35] "kph"'``.
    """
    return (
        'VERSION ""\n\n'
        "NS_ :\n\n"
        "BS_:\n\n"
        "BU_:\n\n"
        f"BO_ {msg_id} {msg_name}: 8 ECU1\n"
        f" SG_ {signal} Vector__XXX\n"
    )


def never_exceeds_yaml(name: str, signal: str, value: str, severity: str) -> str:
    """Return a single-check YAML file with a ``never_exceeds`` condition."""
    return (
        "checks:\n"
        f"  - name: {name}\n"
        f"    signal: {signal}\n"
        "    condition: never_exceeds\n"
        f"    value: {value}\n"
        f"    severity: {severity}\n"
    )
