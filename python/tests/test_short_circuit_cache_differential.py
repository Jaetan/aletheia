# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
"""Short-circuit differential: the cache is readable-set-driven, not eval-driven.

The streaming step extracts every readable signal once per accepted frame and
shares that table between the cache update and predicate evaluation.  A tempting
but WRONG optimization would warm the cache only for the atoms eval actually
reaches — but ``And``/``Or`` short-circuit in ``stepL``, so a signal whose only
atom is short-circuited on a frame would then never be cached, and a later
frame's last-known-value fallback would read ``Unknown`` instead of the real
value.  This test pins the correct (short-circuit-independent) behaviour.

Scenario — ``always(Trigger >= 100  OR  Secret >= 50)`` with ``Trigger`` in
message A and ``Secret`` in message B (SEPARATE messages):

* Frame 1 (msg A): ``Trigger = 500`` → cached.
* Frame 2 (msg B): ``Secret = 30``.  ``Trigger`` falls back to the cached 500,
  which is ``>= 100`` True, so the ``Or`` SHORT-CIRCUITS at ``Trigger`` and eval
  never consults ``Secret``.  The readable-set-driven cache must nonetheless warm
  ``Secret = 30`` from this frame — this is the discriminating step.
* Frame 3 (msg A): ``Trigger = 10`` (``< 100``); ``Secret`` is ABSENT (msg A), so
  the ``Or`` must fall back to the cached ``Secret``.  With ``Secret = 30`` cached
  (``< 50``) the ``Or`` is definitely False → a VIOLATION.  An eval-driven cache
  that skipped the short-circuited ``Secret`` on frame 2 would instead see
  ``Or(False, Unknown) = Unknown`` → an ``ack``, not a violation — a visible
  divergence this golden would catch.
* Frame 4 (msg A): ``Trigger = 20`` — the cached ``Secret = 30`` persists, so the
  violation repeats.

The golden below was captured against the OPTA baseline ``.so`` (the
pre-extract-once kernel) and the extract-once kernel and confirmed
byte-identical; PREFIX / FIXBASE / PROTO baselines all agree, since every correct
implementation drives the cache from the readable set.
"""

from __future__ import annotations

import json
from typing import TYPE_CHECKING

from tests._dbc_helpers import dbc as build_dbc
from tests._dbc_helpers import message, signal

from aletheia import AletheiaClient, Signal
from aletheia.types import DLCCode

# Streaming golden tests share an inherent scaffold — the JSON normalizer, the
# send loop, and the property_batch "fails" enrichment shape — with
# test_readable_filter_semantics (the sibling readable-filter differential).  The
# DBC/signal construction is already factored through tests._dbc_helpers; the
# remaining structural overlap is the golden shape itself, which is the point of
# the test.  Mirrors the same allowance in test_dsl_composition.py.
# pylint: disable=duplicate-code

if TYPE_CHECKING:
    from aletheia.types import DBCDefinition, LTLFormula

_MSG_A = 0x100
_MSG_B = 0x200
_DLC = 8


def _dbc() -> DBCDefinition:
    # Two separate messages so Trigger (msg A) can be present while Secret
    # (msg B) is absent on the same frame — the geometry the short-circuit needs.
    return build_dbc(
        [
            message(_MSG_A, "MsgA", [signal("Trigger")]),
            message(_MSG_B, "MsgB", [signal("Secret")]),
        ]
    )


def _props() -> list[LTLFormula]:
    # always( Trigger >= 100  OR  Secret >= 50 ) — the Or short-circuits at
    # Trigger, so Secret's only atom is skipped on the frames where Trigger holds.
    formula = (
        Signal("Trigger")
        .greater_than_or_equal(100)
        .or_(Signal("Secret").greater_than_or_equal(50))
        .always()
    )
    return [formula.to_dict()]


# (can_id, value) — Trigger goes into message A, Secret into message B.
_SEQ = [
    (_MSG_A, 500),  # Trigger=500 cached (>=100)
    (_MSG_B, 30),  # Secret=30 cached via readable set WHILE the Or short-circuits at Trigger
    (_MSG_A, 10),  # Trigger=10 (<100); Secret absent -> cached 30 (<50) -> Or false -> VIOLATION
    (_MSG_A, 20),  # cached Secret=30 persists -> violation repeats
]


def _frame_bytes(value: int) -> bytearray:
    data = bytearray(_DLC)
    data[0:2] = (value & 0xFFFF).to_bytes(2, "little")
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
        for can_id, value in _SEQ:
            ts += 1000
            out.append(
                _norm(
                    client.send_frame(
                        timestamp=ts,
                        can_id=can_id,
                        dlc=DLCCode(_DLC),
                        data=_frame_bytes(value),
                    )
                )
            )
        out.append(_norm(client.end_stream()))
    return out


_FORMULA = "always(Trigger >= 100 or Secret >= 50)"
_FAIL_REASON = "Atomic: predicate failed"


def _violation(ts: int, trigger: int) -> dict[str, object]:
    """Build the frame's violation entry — Trigger present, Secret from the cached 30."""
    return {
        "type": "property_batch",
        "results": [
            {
                "type": "property",
                "status": "fails",
                "property_index": 0,
                "timestamp": ts,
                "reason": _FAIL_REASON,
                "enrichment": {
                    "signals": {"Trigger": str(trigger)},
                    "formula_desc": _FORMULA,
                    "enriched_reason": (
                        f"Trigger = {trigger} (formula: {_FORMULA}) [core: {_FAIL_REASON}]"
                    ),
                    "core_reason": _FAIL_REASON,
                },
            }
        ],
    }


# Captured against the OPTA baseline .so AND the extract-once kernel and confirmed
# byte-identical.  A cache warmed by eval's short-circuited traversal (rather than
# the readable set) would starve Secret on frame 2, flipping the frame-3/4
# violations to acks — so this literal has teeth.
_GOLDEN: list[object] = [
    {"status": "success", "message": "Properties set successfully"},
    {"status": "ack"},
    {"status": "ack"},
    _violation(3000, 10),
    _violation(4000, 20),
    {
        "status": "complete",
        "results": [{"type": "property", "status": "holds", "property_index": 0}],
        "warnings": [],
    },
]


def test_short_circuit_cache_is_readable_set_driven() -> None:
    """A short-circuited atom's signal must still be cached from the readable set.

    Frame 2's ``Or`` short-circuits at ``Trigger`` (Secret never consulted by
    eval), yet ``Secret`` must be cached so frames 3-4 produce their violations
    from the cached last-known value — proven by byte-identical match to the
    OPTA baseline golden.
    """
    assert _run_scenario() == _GOLDEN
