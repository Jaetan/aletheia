# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
"""Child process for the streaming-residency regression test.

Runs in a *fresh* interpreter so ``resource.getrusage`` reports a peak that
belongs to this streaming session alone.  ``ru_maxrss`` is a process-wide
high-water mark: measured inside the pytest process it would already carry
whatever earlier tests allocated, and a genuine leak could hide under that
baseline.  A dedicated process removes the confound.

Invoked as ``python _residency_child.py <shape> <frames>``; prints one JSON
object on stdout describing the resident-set growth across the run.
"""

from __future__ import annotations

import json
import resource
import sys
import time
from fractions import Fraction
from typing import TYPE_CHECKING

from aletheia import AletheiaClient, Signal
from aletheia._dbc_types import empty_dbc_tier2
from aletheia.types import DLCByteCount, DLCCode

if TYPE_CHECKING:
    from aletheia.types import DBCDefinition, DBCSignal

MESSAGE_ID = 256
DLC_BYTES = 8
EMPTY_MESSAGE = "empty-message"


def peak_kib() -> int:
    """Return this process's peak resident set size in KiB."""
    return resource.getrusage(resource.RUSAGE_SELF).ru_maxrss


def _signal(name: str, start_bit: int) -> DBCSignal:
    """Build one 16-bit unsigned little-endian signal definition."""
    return {
        "name": name,
        "startBit": start_bit,
        "length": 16,
        "byteOrder": "little_endian",
        "signed": False,
        "factor": Fraction(1, 10),
        "offset": Fraction(0),
        "minimum": Fraction(0),
        "maximum": Fraction(6000),
        "unit": "",
        "presence": "always",
        "receivers": [],
    }


def build_dbc(shape: str) -> DBCDefinition:
    """Build the DBC for a residency shape.

    ``empty-message`` carries no signals, so the cache stays empty and the run
    exercises the cache *value* the streaming step derives per frame.
    ``three-signals`` carries three, so the run additionally exercises the
    cache's entry spine.
    """
    signals: list[DBCSignal] = (
        []
        if shape == EMPTY_MESSAGE
        else [_signal("Speed", 0), _signal("RPM", 16), _signal("Temp", 32)]
    )
    return {
        "version": "1.0",
        "messages": [
            {
                "id": MESSAGE_ID,
                "name": "M",
                "dlc": DLCByteCount(DLC_BYTES),
                "sender": "ECU",
                "signals": signals,
            }
        ],
        **empty_dbc_tier2(),
    }


def main() -> int:
    """Stream ``frames`` frames and report the resident-set growth as JSON."""
    shape, frames = sys.argv[1], int(sys.argv[2])
    dbc = build_dbc(shape)
    properties = (
        [] if shape == EMPTY_MESSAGE else [Signal("Speed").less_than(5000).always().to_dict()]
    )

    with AletheiaClient() as client:
        client.parse_dbc(dbc)
        client.set_properties(properties)
        client.start_stream()
        baseline = peak_kib()
        started = time.monotonic()
        for i in range(frames):
            raw = (i * 7) % 60000
            payload = bytearray(DLC_BYTES)
            payload[0:2] = (raw & 0xFFFF).to_bytes(2, "little")
            payload[2:4] = ((raw * 3) & 0xFFFF).to_bytes(2, "little")
            payload[4:6] = ((raw // 7) & 0xFFFF).to_bytes(2, "little")
            client.send_frame(
                timestamp=(i + 1) * 1000, can_id=MESSAGE_ID, dlc=DLCCode(DLC_BYTES), data=payload
            )
        elapsed = time.monotonic() - started
        peak = peak_kib()
        client.end_stream()

    json.dump(
        {
            "shape": shape,
            "frames": frames,
            "baseline_kib": baseline,
            "peak_kib": peak,
            "growth_kib": peak - baseline,
            "fps": frames / elapsed if elapsed > 0 else 0.0,
        },
        sys.stdout,
    )
    return 0


if __name__ == "__main__":
    sys.exit(main())
