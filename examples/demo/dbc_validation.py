# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
"""DBC Validation Demo.

Aletheia validates DBC files during parse_dbc(), distinguishing hard errors from
warnings:
  - Signal overlap (unless multiplexed to different mux values) is an ERROR — the
    DBC is rejected (response status "error").
  - minimum > maximum is a WARNING — the DBC still parses (status "success") with
    a ``min_exceeds_max`` issue flagged for the caller.

Requirements:
    - Aletheia built: `cabal run shake -- build`
"""

# Standalone teaching demos intentionally repeat small setup/teardown
# patterns (a local CANFrame, the send-frame loop, the __main__ guard) so
# each script reads and runs in isolation; deduplicating would couple them.
# pylint: disable=duplicate-code

from __future__ import annotations

import sys
from fractions import Fraction
from typing import TYPE_CHECKING, cast

from aletheia import AletheiaClient, AletheiaError

if TYPE_CHECKING:
    from aletheia.types import DBCDefinition

# The demo DBCs use exact Fraction scaling params (the float principle — never a
# float; 0.1 is Fraction(1, 10), 655.35 is Fraction(65535, 100)) and are partial /
# some intentionally invalid to exercise the parser's validation, so they are
# cast to DBCDefinition rather than constructed as the strict TypedDict.


def create_valid_dbc() -> DBCDefinition:
    """Non-overlapping signals: Temperature[0:15], Pressure[16:31], Status[32:39]."""
    return cast(
        "DBCDefinition",
        {
            "version": "1.0",
            "messages": [
                {
                    "id": 256,
                    "name": "SensorData",
                    "dlc": 8,
                    "sender": "ECU",
                    "signals": [
                        {
                            "name": "Temperature",
                            "startBit": 0,
                            "length": 16,
                            "byteOrder": "little_endian",
                            "signed": True,
                            "factor": Fraction(1, 10),
                            "offset": -40,
                            "minimum": -40,
                            "maximum": 215,
                            "unit": "C",
                            "presence": "always",
                        },
                        {
                            "name": "Pressure",
                            "startBit": 16,
                            "length": 16,
                            "byteOrder": "little_endian",
                            "signed": False,
                            "factor": Fraction(1, 100),
                            "offset": 0,
                            "minimum": 0,
                            "maximum": Fraction(65535, 100),  # 655.35
                            "unit": "bar",
                            "presence": "always",
                        },
                        {
                            "name": "Status",
                            "startBit": 32,
                            "length": 8,
                            "byteOrder": "little_endian",
                            "signed": False,
                            "factor": 1,
                            "offset": 0,
                            "minimum": 0,
                            "maximum": 255,
                            "unit": "",
                            "presence": "always",
                        },
                    ],
                }
            ],
        },
    )


def create_overlapping_dbc() -> DBCDefinition:
    """Overlapping signals: Temperature[0:15] and Pressure[8:23] share bits 8-15."""
    return cast(
        "DBCDefinition",
        {
            "version": "1.0",
            "messages": [
                {
                    "id": 256,
                    "name": "SensorData",
                    "dlc": 8,
                    "sender": "ECU",
                    "signals": [
                        {
                            "name": "Temperature",
                            "startBit": 0,
                            "length": 16,
                            "byteOrder": "little_endian",
                            "signed": True,
                            "factor": Fraction(1, 10),
                            "offset": -40,
                            "minimum": -40,
                            "maximum": 215,
                            "unit": "C",
                            "presence": "always",
                        },
                        {
                            "name": "Pressure",
                            "startBit": 8,
                            "length": 16,
                            "byteOrder": "little_endian",
                            "signed": False,
                            "factor": Fraction(1, 100),
                            "offset": 0,
                            "minimum": 0,
                            "maximum": Fraction(65535, 100),  # 655.35
                            "unit": "bar",
                            "presence": "always",
                        },
                    ],
                }
            ],
        },
    )


def create_inconsistent_range_dbc() -> DBCDefinition:
    """Temperature minimum=100 > maximum=50."""
    return cast(
        "DBCDefinition",
        {
            "version": "1.0",
            "messages": [
                {
                    "id": 256,
                    "name": "SensorData",
                    "dlc": 8,
                    "sender": "ECU",
                    "signals": [
                        {
                            "name": "Temperature",
                            "startBit": 0,
                            "length": 16,
                            "byteOrder": "little_endian",
                            "signed": True,
                            "factor": Fraction(1, 10),
                            "offset": -40,
                            "minimum": 100,
                            "maximum": 50,
                            "unit": "C",
                            "presence": "always",
                        },
                    ],
                }
            ],
        },
    )


def create_multiplexed_dbc() -> DBCDefinition:
    """SensorA[8:23] and SensorB[8:23] overlap but are multiplexed (MuxSelector=0 vs 1)."""
    return cast(
        "DBCDefinition",
        {
            "version": "1.0",
            "messages": [
                {
                    "id": 256,
                    "name": "MultiplexedData",
                    "dlc": 8,
                    "sender": "ECU",
                    "signals": [
                        {
                            "name": "MuxSelector",
                            "startBit": 0,
                            "length": 8,
                            "byteOrder": "little_endian",
                            "signed": False,
                            "factor": 1,
                            "offset": 0,
                            "minimum": 0,
                            "maximum": 3,
                            "unit": "",
                            "presence": "always",
                        },
                        {
                            "name": "SensorA",
                            "startBit": 8,
                            "length": 16,
                            "byteOrder": "little_endian",
                            "signed": False,
                            "factor": Fraction(1, 10),
                            "offset": 0,
                            "minimum": 0,
                            "maximum": Fraction(65535, 10),  # 6553.5
                            "unit": "rpm",
                            "presence": "multiplexed",
                            "multiplexor": "MuxSelector",
                            "multiplex_values": [0],
                        },
                        {
                            "name": "SensorB",
                            "startBit": 8,
                            "length": 16,
                            "byteOrder": "little_endian",
                            "signed": True,
                            "factor": Fraction(1, 100),
                            "offset": 0,
                            "minimum": Fraction(-32768, 100),  # -327.68
                            "maximum": Fraction(32767, 100),  # 327.67
                            "unit": "m/s",
                            "presence": "multiplexed",
                            "multiplexor": "MuxSelector",
                            "multiplex_values": [1],
                        },
                    ],
                }
            ],
        },
    )


def check_dbc(
    name: str,
    dbc: DBCDefinition,
    *,
    expect_valid: bool,
    expect_warning: str | None = None,
) -> bool:
    """Parse a DBC and check its status, and optionally an expected warning code.

    ``expect_valid`` is the hard accept/reject outcome (status "success" vs
    "error"); ``expect_warning`` additionally asserts a non-fatal warning code is
    present (e.g. ``min_exceeds_max`` — a warning that flags but does not reject).

    A successful ``parse_dbc`` returns ``{status, dbc, warnings}`` — the
    non-fatal codes live under ``warnings`` (the ``issues`` key is the
    *validate* path, which merges errors and warnings into one list).
    """
    try:
        with AletheiaClient() as client:
            response = client.parse_dbc(dbc)

            valid = response.get("status") == "success"
            warnings = response.get("warnings", [])
            warned = expect_warning is None or any(
                isinstance(warning, dict) and warning.get("code") == expect_warning
                for warning in warnings
            )
            passed = valid == expect_valid and warned
            status = "VALID" if valid else "INVALID"
            verdict = "PASS" if passed else "FAIL"

            print(f"  {name}: {status} — {verdict}")
            msg = response.get("message", "")
            if msg:
                print(f"    {msg}")
            if expect_warning is not None:
                print(f"    warning {expect_warning!r}: {'present' if warned else 'MISSING'}")
            return passed

    except AletheiaError as e:
        print(f"  {name}: ERROR — {e}")
        return False


def main() -> None:
    """Run the DBC-validation scenarios and print a pass/fail summary."""
    print("=" * 60)
    print("DBC VALIDATION DEMO")
    print("=" * 60)

    results = [
        check_dbc("Valid DBC (no overlap)", create_valid_dbc(), expect_valid=True),
        check_dbc("Overlapping signals", create_overlapping_dbc(), expect_valid=False),
        check_dbc(
            "Inconsistent range (min > max) — warns, not rejected",
            create_inconsistent_range_dbc(),
            expect_valid=True,
            expect_warning="min_exceeds_max",
        ),
        check_dbc("Multiplexed (overlap OK)", create_multiplexed_dbc(), expect_valid=True),
    ]

    passed = sum(results)
    total = len(results)

    print(f"\n{passed}/{total} tests passed")

    print("\n" + "=" * 60)
    print("DONE")
    print("=" * 60)

    # Exit non-zero on any failed scenario so the demo gate (test_demo_scripts)
    # sees a truthful return code instead of passing vacuously on "N/4".
    if passed != total:
        sys.exit(1)


if __name__ == "__main__":
    main()
