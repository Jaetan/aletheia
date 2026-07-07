# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
"""Regression: ``aletheia check --excel`` accepts an Excel-authored DBC end-to-end.

The Excel schema has no transmitter column, so ``excel_loader`` builds every
message with a placeholder sender. It used to use the empty string, which is not
a valid DBC identifier: the kernel's DBC text parser rejected it, so
``check``/``signals``/``validate --excel`` exited 2 ("``''`` is not a valid DBC
identifier") on *every* workbook — the technician's Excel on-ramp was broken
end-to-end, and no test exercised the Excel→kernel round-trip. The loader now
emits the reserved ``Vector__XXX`` "no transmitter assigned" placeholder (a valid
identifier that legitimately repeats across messages).

The failure was in the kernel's parse of the Excel-derived DBC text, so only an
end-to-end run through the FFI exercises it. Fixtures are generated in
``tmp_path``. See ``_cli_check_helpers`` for the shared subprocess scaffolding.
"""

from __future__ import annotations

from typing import TYPE_CHECKING

from _cli_check_helpers import report, run_check, skip_without_ffi
from _excel_helpers import active_sheet
from openpyxl import Workbook

from aletheia.excel_loader import CHECKS_HEADERS, DBC_HEADERS

if TYPE_CHECKING:
    from pathlib import Path

# candump frame: 0x100 VehicleSpeed raw 0x0258 = 600 -> 6.00 kph (under the 120
# limit), so a well-formed run passes and exits 0 — never the exit-2 parse error.
_LOG = "(0.000000) can0 100#5802000000000000\n"

# One VehicleDynamics message + one VehicleSpeed signal, positionally aligned to
# the canonical DBC_HEADERS (blank Extended / Multiplexor / Multiplex Value are
# None, which the loader skips). Numeric cells are TEXT (the exact-value contract
# — a number cell stores a lossy float). No transmitter column: the crux.
_DBC_ROW = [
    "0x100",
    "VehicleDynamics",
    None,
    "8",
    "VehicleSpeed",
    "0",
    "16",
    "little_endian",
    "FALSE",
    "0.01",
    "0",
    "0",
    "655.35",
    "kph",
    None,
    None,
]
_CHECK_ROW = ["Speed limit", "VehicleSpeed", "never_exceeds", "120", None, None, None, "safety"]


def _write_workbook(path: Path) -> None:
    """Write a minimal DBC+Checks workbook with NO transmitter column."""
    wb = Workbook()
    dbc = active_sheet(wb)
    dbc.title = "DBC"
    dbc.append(DBC_HEADERS)
    dbc.append(_DBC_ROW)
    checks = wb.create_sheet("Checks")
    checks.append(CHECKS_HEADERS)
    checks.append(_CHECK_ROW)
    wb.save(str(path))


def test_check_excel_dbc_is_accepted_by_the_kernel(tmp_path: Path) -> None:
    """An Excel-authored DBC round-trips through the kernel — not rejected for an empty sender.

    On the unpatched loader this exits 2 with "``''`` is not a valid DBC
    identifier"; with the ``Vector__XXX`` placeholder the DBC parses and the
    (satisfied) check exits 0.
    """
    skip_without_ffi()

    workbook = tmp_path / "checks.xlsx"
    _write_workbook(workbook)
    log_path = tmp_path / "drive.log"
    log_path.write_text(_LOG, encoding="utf-8")

    result = run_check(["--excel", str(workbook), str(log_path)])
    msg = report(result)
    # The bug: the empty sender was rejected as an invalid DBC identifier.
    assert "not a valid DBC identifier" not in (result.stdout + result.stderr), msg
    # The DBC parses and the satisfied check passes → exit 0 (never the exit-2 parse error).
    assert result.returncode == 0, msg
