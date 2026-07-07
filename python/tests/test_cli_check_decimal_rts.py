# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
"""Regression: ``aletheia check`` with a DECIMAL threshold in a fresh process.

A decimal check threshold (e.g. ``value: 199.5`` — ubiquitous in automotive:
voltages, pressures, speeds) is parsed exactly through the kernel's
``from_decimal`` SSOT, which is RTS-gated and *vocal*: it never self-initialises
the GHC runtime. ``_cmd_check`` used to load the check files BEFORE any client
(and thus any ``FFIBackend``) existed, so in a fresh process (RTS down) the load
raised ``GHC runtime not initialized ... from_decimal does not self-initialise
the RTS`` and the command died with exit 2 before streaming a single frame —
breaking ``check`` on *any* check file with a decimal threshold. The fix brings
the RTS up first (constructing the production ``FFIBackend``) and injects it into
the client, so the check files load with the runtime already up.

Fixtures are generated in ``tmp_path`` (self-contained — no committed asset). See
``_cli_check_helpers`` for the shared subprocess scaffolding and why a subprocess
(not in-process ``main()``) is required.
"""

from __future__ import annotations

from typing import TYPE_CHECKING

import can
from _cli_check_helpers import dbc_text, never_exceeds_yaml, report, run_check, skip_without_ffi

if TYPE_CHECKING:
    from pathlib import Path

# EngineSpeed factor 0.25: raw 800 decodes to 200.0 rpm, over the 199.5 limit.
_SIGNAL = 'EngineSpeed : 0|16@1+ (0.25,0) [0|8000] "rpm"'


def test_check_decimal_threshold_streams_end_to_end(tmp_path: Path) -> None:
    """A decimal-threshold check runs end-to-end (no RTS error) and reports its violation.

    Would have caught the RTS-ordering bug: on the unpatched code this run dies
    with exit 2 and ``GHC runtime not initialized`` on stderr, because the
    decimal threshold is parsed before any backend brings the runtime up.
    """
    skip_without_ffi()

    dbc_path = tmp_path / "engine.dbc"
    dbc_path.write_text(dbc_text(256, "EngineStatus", _SIGNAL), encoding="utf-8")
    # The DECIMAL threshold (199.5) is the crux: the YAML no-float loader keeps it
    # a string and parses it via the RTS-gated ``from_decimal`` SSOT during
    # check-loading — the exact step that used to run before any RTS existed.
    checks_path = tmp_path / "checks.yaml"
    checks_path.write_text(
        never_exceeds_yaml("Speed limit", "EngineSpeed", "199.5", "critical"), encoding="utf-8"
    )

    # One monotonic frame; EngineSpeed raw 0x0320 = 800 -> 200.0 rpm (> 199.5).
    log_path = tmp_path / "drive.asc"
    writer = can.ASCWriter(str(log_path))
    writer.on_message_received(
        can.Message(
            timestamp=1.0,
            arbitration_id=0x100,
            data=bytes([0x20, 0x03, 0, 0, 0, 0, 0, 0]),
            is_extended_id=False,
        )
    )
    writer.stop()

    result = run_check(["--dbc", str(dbc_path), "--checks", str(checks_path), str(log_path)])
    msg = report(result)
    # The bug: from_decimal raised because the RTS was still down when the
    # decimal check threshold was parsed during check-loading.
    assert "GHC runtime not initialized" not in result.stderr, msg
    # EngineSpeed reaches 200 rpm, over the 199.5 limit, so the run reports a
    # violation and exits 1 — not the exit-2 operational error the RTS failure
    # produced.
    assert result.returncode == 1, msg
    assert "EngineSpeed" in result.stdout, msg
    assert "violation" in result.stdout.lower(), msg
