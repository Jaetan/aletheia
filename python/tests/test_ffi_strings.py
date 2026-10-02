# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
"""The kernel reads and writes its strings as UTF-8, whatever the locale.

Every string crossing the C boundary is UTF-8 on both sides: the kernel decodes
the caller's bytes as UTF-8 and answers UTF-8, so neither the verdict on an
input nor the text of a response depends on the locale of the process that
loaded the library.  Bytes that are not UTF-8 are refused, never dropped.
"""

from __future__ import annotations

import json
import os
import subprocess
import sys
from pathlib import Path
from typing import Final

from _locale_child import SENTINEL

from aletheia import FFIBackend

_CHILD: Final = Path(__file__).parent / "_locale_child.py"


def test_kernel_strings_do_not_depend_on_the_locale() -> None:
    """Under ``LC_ALL=C`` non-ASCII text crosses the kernel intact both ways."""
    env = dict(os.environ)
    env["PYTHONPATH"] = os.pathsep.join(p for p in sys.path if p)
    env["LC_ALL"] = "C"
    completed = subprocess.run(
        [sys.executable, str(_CHILD)],
        capture_output=True,
        encoding="utf-8",
        check=False,
        env=env,
    )
    report = f"stdout: {completed.stdout}\nstderr: {completed.stderr}"
    assert completed.returncode == 0, report
    assert completed.stdout.splitlines()[-1:] == [SENTINEL], report


def test_process_refuses_input_it_cannot_read_whole() -> None:
    """A command with a byte that is not UTF-8, or with a NUL, is refused whole.

    Neither is read without the offending bytes: before, the first lost its
    byte and the second ended at the NUL, each running a command the caller
    did not send.
    """
    backend = FFIBackend()
    state = backend.init()
    try:
        for command, reason in (
            (b'{"type": "command", "command": "no\xff"}', "input is not valid UTF-8"),
            (b'{"type": "command", "command": "validateDBC"}\x00{"x"', "input contains a NUL byte"),
        ):
            response = json.loads(backend.process(state, command))
            assert response == {
                "status": "error",
                "code": "ffi_validation_error",
                "message": reason,
            }, command
    finally:
        backend.close(state)
