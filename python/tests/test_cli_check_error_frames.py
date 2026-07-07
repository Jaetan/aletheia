# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
"""Regression: ``aletheia check`` must not silently swallow per-frame errors.

The streaming check pipeline (``checks_runner._process_frames``) used to act
only on ``property_batch`` responses and drop everything else — including a
per-frame ``ErrorResponse``. So when the kernel refused a frame (e.g. a
non-monotonic timestamp, which its metric-LTL operators require to be
monotonic), that error was dropped and the run reported "all checks passed"
with exit 0. A *formally verified safety tool reporting PASS on frames it could
not evaluate* is a false negative — the worst failure mode for the guarantee the
tool advertises. Real captures with clock resets or multi-source merges routinely
carry non-monotonic timestamps, so this is not a corner case.

The fix routes each frame response through ``raise_on_error_response`` (the same
fail-fast contract ``send_frames`` already enforces): a per-frame ``ErrorResponse``
raises ``BatchError`` (an ``AletheiaError``), which the CLI renders and exits 2.

Fixtures are generated in ``tmp_path`` — no committed asset. See
``_cli_check_helpers`` for the shared subprocess scaffolding.
"""

from __future__ import annotations

from typing import TYPE_CHECKING

from _cli_check_helpers import dbc_text, never_exceeds_yaml, report, run_check, skip_without_ffi

if TYPE_CHECKING:
    from pathlib import Path

_SIGNAL = 'VehicleSpeed : 0|16@1+ (0.01,0) [0|655.35] "kph"'

# Three candump frames whose timestamps go 0.0 -> 1.0 -> 0.5: the third rewinds
# the clock, so the kernel rejects it (handler_non_monotonic_timestamp). None of
# the three speeds (raw 0x0258=600 -> 6 kph, etc.) violates the 120 kph limit, so
# on the BUGGY code the run reports "all checks passed" / exit 0 — the false PASS.
_NONMONOTONIC_LOG = (
    "(0.000000) can0 100#5802000000000000\n"
    "(1.000000) can0 100#0a03000000000000\n"
    "(0.500000) can0 100#2003000000000000\n"
)


def test_check_rejects_non_monotonic_log_instead_of_false_pass(tmp_path: Path) -> None:
    """A non-monotonic trace exits 2 with the kernel error — never a false 'all passed'.

    On the unpatched pipeline the per-frame error is swallowed and the run prints
    "all checks passed" / exit 0. The fix surfaces it: exit 2, with the
    non-monotonic-timestamp error, and no pass claim.
    """
    skip_without_ffi()

    dbc_path = tmp_path / "vehicle.dbc"
    dbc_path.write_text(dbc_text(256, "VehicleDynamics", _SIGNAL), encoding="utf-8")
    checks_path = tmp_path / "checks.yaml"
    checks_path.write_text(
        never_exceeds_yaml("Speed limit", "VehicleSpeed", "120", "safety"), encoding="utf-8"
    )
    log_path = tmp_path / "drive.log"
    log_path.write_text(_NONMONOTONIC_LOG, encoding="utf-8")

    result = run_check(["--dbc", str(dbc_path), "--checks", str(checks_path), str(log_path)])
    msg = report(result)
    combined = (result.stdout + result.stderr).lower()
    # The false-PASS symptom the bug produced.
    assert "all checks passed" not in result.stdout, msg
    # Operational error, per the CLI's documented 0/1/2 contract.
    assert result.returncode == 2, msg
    # The specific kernel rejection must be surfaced, not swallowed.
    assert "non-monotonic" in combined, msg
