# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
"""The runtime heap cap contains: the process ends, and the host lives.

The heap cap is not a recoverable error: when it fires the process terminates
(a GHC HeapExhausted abort) so the host survives. A subprocess boots the real
FFI client with the default cap and processes a workload, and a second boots it
under a tight ``ALETHEIA_RTS_OPTS=-M12M`` cap over a large DBC and must abort
(non-zero exit, no success sentinel). Both run out of process because the
abort ends the process and the GHC runtime starts once per process.
"""

from __future__ import annotations

import os
import subprocess
import sys
from typing import NamedTuple, NewType

import pytest

from aletheia.client._ffi import RTS_OVERRIDE_ENV, find_ffi_library
from aletheia.common_types import ExitStatus, Prose

# How many messages the workload's DBC declares.
MessageCount = NewType("MessageCount", int)
# The flags a caller appends to the runtime's own through RTS_OVERRIDE_ENV.
RtsOptions = NewType("RtsOptions", str)

# The subprocess workload: boot the real FFI client and parse a VALID DBC of
# `argv[1]` messages.  A large count builds a live parse tree well past a tight
# -M cap, so the cap fires mid-parse (the process aborts); a small count fits any
# cap and completes.  The sentinel is printed only on a clean finish; a parse
# error (which a valid DBC never produces) exits 3, distinct from the abort.
_WORKLOAD = r"""
import sys
from aletheia import AletheiaClient

n = int(sys.argv[1])
lines = ['VERSION ""', "", "NS_ :", "", "BS_:", "", "BU_: ECU", ""]
for i in range(n):
    lines.append(f"BO_ {256 + i} Msg{i}: 8 ECU")
    lines.append(f' SG_ Sig{i} : 0|16@1+ (0.25,0) [0|8000] "u" ECU')
    lines.append("")
dbc = "\n".join(lines)
with AletheiaClient() as client:
    resp = client.parse_dbc_text(dbc)
    if isinstance(resp, dict) and resp.get("status") == "error":
        sys.exit(3)
print("ALETHEIA_RTS_OK")
"""

_SENTINEL = "ALETHEIA_RTS_OK"


def _skip_without_ffi() -> None:
    """Skip the calling test if libaletheia-ffi.so cannot be resolved."""
    try:
        find_ffi_library()
    except FileNotFoundError:
        pytest.skip("libaletheia-ffi.so not found — run 'cabal run shake -- build'")


class WorkloadRun(NamedTuple):
    """How the workload's process ended and what it wrote."""

    returncode: ExitStatus
    stdout: Prose
    stderr: Prose


def _run_workload(n: MessageCount, rts_options: RtsOptions | None) -> WorkloadRun:
    """Run the DBC-parse workload out of process, its runtime given ``rts_options`` when set."""
    env = os.environ.copy()
    if rts_options is not None:
        env[RTS_OVERRIDE_ENV] = rts_options
    done = subprocess.run(
        [sys.executable, "-c", _WORKLOAD, str(n)],
        env=env,
        capture_output=True,
        text=True,
        check=False,
    )
    return WorkloadRun(ExitStatus(done.returncode), Prose(done.stdout), Prose(done.stderr))


def test_default_cap_boots_and_processes() -> None:
    """The correct path (hs_init_with_rtsopts + -M3G) boots and processes a workload."""
    _skip_without_ffi()
    result = _run_workload(MessageCount(5), None)
    assert result.returncode == 0, result.stderr
    assert _SENTINEL in result.stdout


def test_tight_cap_aborts_the_process() -> None:
    """A tight cap over a large workload TERMINATES the process (containment-by-abort).

    The teeth of the whole feature: with ``ALETHEIA_RTS_OPTS=-M12M`` the parse of
    a large DBC exceeds the cap and GHC aborts the process — a non-zero exit with
    no success sentinel, never a recoverable error.
    """
    _skip_without_ffi()
    result = _run_workload(MessageCount(1000), RtsOptions("-M12M"))
    assert result.returncode != 0, "the tight cap must abort the process"
    assert _SENTINEL not in result.stdout
    # Exit 3 is the workload's own parse-error path; a valid DBC never takes it,
    # so a non-zero, non-3 exit is the GHC heap abort (containment), not a masked
    # parse failure.
    assert result.returncode != 3, f"unexpected parse error, not a heap abort: {result.stderr}"
