# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
"""Shared scaffolding for the hermetic ``aletheia check`` CLI regression tests.

Each such test generates its own fixtures in ``tmp_path`` and drives ``aletheia
check`` as a SUBPROCESS against the real ``build/libaletheia-ffi.so``: the GHC
RTS is process-global and one-shot, so a subprocess keeps each test independent
of RTS state an earlier test may have established. This module centralises the
subprocess invocation, the FFI-missing skip, and the failure report so the
individual test files carry only their own fixture content and assertions
(and do not trip pylint's duplicate-code detector on the shared boilerplate).
"""

from __future__ import annotations

import os
import subprocess
import sys
from pathlib import Path

import pytest

REPO_ROOT = Path(__file__).resolve().parents[2]
FFI_LIB = REPO_ROOT / "build" / "libaletheia-ffi.so"
_SUBPROCESS_CWD = REPO_ROOT / "python"
_RUN_TIMEOUT_S = 180


def skip_without_ffi() -> None:
    """Skip the calling test if the FFI shared library has not been built."""
    if not FFI_LIB.exists():
        pytest.skip(f"libaletheia-ffi.so missing at {FFI_LIB} — run 'cabal run shake -- build'")


def run_check(args: list[str]) -> subprocess.CompletedProcess[str]:
    """Run ``aletheia check <args>`` as a subprocess against the real ``.so``."""
    env = dict(os.environ)
    env["ALETHEIA_LIB"] = str(FFI_LIB)
    return subprocess.run(
        [sys.executable, "-m", "aletheia", "check", *args],
        cwd=_SUBPROCESS_CWD,
        env=env,
        capture_output=True,
        text=True,
        timeout=_RUN_TIMEOUT_S,
        check=False,
    )


def report(result: subprocess.CompletedProcess[str]) -> str:
    """Render a completed subprocess as a human-readable assertion message."""
    return (
        f"exit={result.returncode}\n"
        f"--- stdout ---\n{result.stdout}\n"
        f"--- stderr ---\n{result.stderr}"
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
