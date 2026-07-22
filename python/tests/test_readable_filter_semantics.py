# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
"""Semantics guard for the readable-signal cache-update filter.

The streaming step only caches signals that some active predicate can read
(``readableSignals`` over the active property atoms); signals no predicate
consults are dropped before extraction.  That is a performance optimization and
MUST be observationally invisible, so this test pins the exact verdict and
enrichment sequence a scenario produces across the cache-reading predicate
families whose result a *too-narrow* filter would corrupt:

* ``changed_by`` (delta) reads the cached PREVIOUS value — a starved atom signal
  would leave it ``Pending`` forever, so the frame-4 satisfaction would vanish.
* a value predicate and a metric-LTL (``for_at_least``) shape over ``Speed``,
  which appears in message A then goes ABSENT in the message-B frames — their
  verdicts must come from the cached last-known value.
* ``always(Level < 150)`` violates even on message-A frames where ``Level`` is
  absent (``signals: {}`` in the enrichment), via the cached ``Level`` — a
  definite fallback verdict a too-narrow filter would flip to ``ack``.

Two NON-ATOM signals (``PadA``, ``Junk``) sit in every frame and are referenced
by no property; the filter drops them, which the identical golden proves is
invisible.  The golden was captured against the pre-filter kernel and the
filtered kernel and confirmed byte-identical.
"""

from __future__ import annotations

import json
from fractions import Fraction
from typing import TYPE_CHECKING

from aletheia import AletheiaClient, Signal
from aletheia._dbc_types import empty_dbc_tier2
from aletheia.types import DLCByteCount, DLCCode

if TYPE_CHECKING:
    from aletheia.types import DBCDefinition, DBCSignal, LTLFormula

_MSG_A = 0x100
_MSG_B = 0x200
_DLC = 8


def _sig(name: str, start_bit: int) -> DBCSignal:
    """Build a 16-bit unsigned little-endian signal (factor 1, wide range)."""
    return {
        "name": name,
        "startBit": start_bit,
        "length": 16,
        "byteOrder": "little_endian",
        "signed": False,
        "factor": Fraction(1),
        "offset": Fraction(0),
        "minimum": Fraction(0),
        "maximum": Fraction(65535),
        "unit": "",
        "presence": "always",
        "receivers": [],
    }


def _dbc() -> DBCDefinition:
    return {
        "version": "1.0",
        "messages": [
            {
                "id": _MSG_A,
                "name": "MsgA",
                "dlc": DLCByteCount(_DLC),
                "sender": "ECU",
                "signals": [_sig("Speed", 0), _sig("PadA", 16)],
            },
            {
                "id": _MSG_B,
                "name": "MsgB",
                "dlc": DLCByteCount(_DLC),
                "sender": "ECU",
                "signals": [_sig("Level", 0), _sig("Junk", 16)],
            },
        ],
        **empty_dbc_tier2(),
    }


def _props() -> list[LTLFormula]:
    return [
        Signal("Level").changed_by(50).eventually().to_dict(),  # delta: reads cached prev
        Signal("Speed").less_than(600).always().to_dict(),  # value pred; Speed goes absent
        Signal("Speed").less_than(600).for_at_least(3000).to_dict(),  # metric-LTL over absent sig
        Signal("Level").less_than(150).always().to_dict(),  # violates; fallback on A frames
    ]


# (message-A?, signal value, pad/junk value) — deterministic.
_SEQ = [
    (True, 500, 111),  # A: Speed=500 cached
    (False, 100, 222),  # B: Level=100 (Pending); Speed fallback 500
    (False, 120, 222),  # B: Level=120 (diff 20 < 50)
    (False, 200, 222),  # B: Level=200 (diff 80 >= 50 -> changed_by satisfied; Level<150 fails)
    (True, 550, 111),  # A: Speed=550; Level absent -> Level<150 fails via cached 200 (signals {})
    (False, 210, 222),  # B: Level=210
    (True, 590, 111),  # A: Speed=590; Level absent fallback
    (False, 300, 222),  # B: Level=300
]


def _frame_bytes(value: int, pad: int) -> bytearray:
    data = bytearray(_DLC)
    data[0:2] = (value & 0xFFFF).to_bytes(2, "little")
    data[2:4] = (pad & 0xFFFF).to_bytes(2, "little")
    return data


def _norm(resp: object) -> object:
    """JSON round-trip so ``Fraction`` enrichment values compare as strings."""
    return json.loads(json.dumps(resp, default=str))


def _run_scenario() -> list[object]:
    """Drive the streaming session; return set + per-frame + end responses."""
    out: list[object] = []
    with AletheiaClient() as client:
        parse = client.parse_dbc(_dbc())
        assert parse.get("status") == "success", parse
        out.append(_norm(client.set_properties(_props())))
        client.start_stream()
        ts = 0
        for a_msg, value, pad in _SEQ:
            ts += 1000
            out.append(
                _norm(
                    client.send_frame(
                        timestamp=ts,
                        can_id=_MSG_A if a_msg else _MSG_B,
                        dlc=DLCCode(_DLC),
                        data=_frame_bytes(value, pad),
                    )
                )
            )
        out.append(_norm(client.end_stream()))
    return out


# Captured against BOTH the pre-filter kernel and the filtered kernel and
# confirmed byte-identical. A too-narrow filter (starving Level or Speed) would
# drop the frame-4 changed_by satisfaction, the fallback Level<150 violations on
# the absent-Level A frames, and the end-of-stream holds — so this literal has
# teeth.
_FAIL_REASON = "Atomic: predicate failed"


def _fails_entry(idx: int, ts: int, signals: dict[str, str], enriched: str) -> dict[str, object]:
    return {
        "enrichment": {
            "core_reason": _FAIL_REASON,
            "enriched_reason": enriched,
            "formula_desc": "always(Level < 150)",
            "signals": signals,
        },
        "property_index": idx,
        "reason": _FAIL_REASON,
        "status": "fails",
        "timestamp": ts,
        "type": "property",
    }


_L150 = "always(Level < 150)"
_GOLDEN: list[object] = [
    {"message": "Properties set successfully", "status": "success"},
    {"status": "ack"},
    {"status": "ack"},
    {"status": "ack"},
    {
        "results": [
            {"property_index": 0, "status": "holds", "type": "property"},
            _fails_entry(
                3, 4000, {"Level": "200"}, f"Level = 200 (formula: {_L150}) [core: {_FAIL_REASON}]"
            ),
        ],
        "type": "property_batch",
    },
    {
        "results": [_fails_entry(3, 5000, {}, f"violated: {_L150} [core: {_FAIL_REASON}]")],
        "type": "property_batch",
    },
    {
        "results": [
            _fails_entry(
                3, 6000, {"Level": "210"}, f"Level = 210 (formula: {_L150}) [core: {_FAIL_REASON}]"
            )
        ],
        "type": "property_batch",
    },
    {
        "results": [_fails_entry(3, 7000, {}, f"violated: {_L150} [core: {_FAIL_REASON}]")],
        "type": "property_batch",
    },
    {
        "results": [
            _fails_entry(
                3, 8000, {"Level": "300"}, f"Level = 300 (formula: {_L150}) [core: {_FAIL_REASON}]"
            )
        ],
        "type": "property_batch",
    },
    {
        "results": [
            {"property_index": 1, "status": "holds", "type": "property"},
            {"property_index": 2, "status": "holds", "type": "property"},
            {"property_index": 3, "status": "holds", "type": "property"},
        ],
        "status": "complete",
        "warnings": [],
    },
]


def test_readable_filter_preserves_verdicts_and_enrichment() -> None:
    """The cache-update filter must not move any verdict or enrichment.

    Delta (``changed_by``), value-fallback, metric-LTL, and violation-enrichment
    across a scenario with unread non-atom signals present in every frame.
    """
    assert _run_scenario() == _GOLDEN
