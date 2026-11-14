# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
"""``send_frame`` enriches a violation from the extraction of the frame's own message.

The enrichment extracts the violating frame under its own identity, the
extended bit included, so a 29-bit frame reads the 29-bit message that
declares its signal.
"""

from __future__ import annotations

from fractions import Fraction
from typing import TYPE_CHECKING

import pytest
from _dbc_helpers import dbc, message, signal

from aletheia import AletheiaClient, Signal
from aletheia.types import DLCCode

if TYPE_CHECKING:
    from aletheia.types import PropertyBatchResponse, PropertyResultEntry, ViolationEnrichment

# ``set_properties`` renders each formula's rational threshold via the kernel,
# which needs the GHC runtime up.
pytestmark = pytest.mark.usefixtures("rts_up")

# A 29-bit id past the 11-bit range, so it names an extended message only.
_EXTENDED_ID = 0x18FF0001

_FORMULA = "always(Speed < 100)"
_FAIL_REASON = "Atomic: predicate failed"


def test_an_extended_frame_violation_is_enriched_from_its_own_message() -> None:
    """A violating 29-bit frame carries the value its extended message declares."""
    extended_message = message(_EXTENDED_ID, "ExtMsg", [signal("Speed")])
    extended_message["extended"] = True
    with AletheiaClient() as client:
        client.parse_dbc(dbc([extended_message]))
        client.set_properties([Signal("Speed").less_than(100).always().to_dict()])
        client.start_stream()
        reply = client.send_frame(
            timestamp=1000,
            can_id=_EXTENDED_ID,
            dlc=DLCCode(8),
            data=bytearray([200, 0, 0, 0, 0, 0, 0, 0]),
            extended=True,
        )
    enrichment: ViolationEnrichment = {
        "signals": {"Speed": Fraction(200)},
        "formula_desc": _FORMULA,
        "enriched_reason": f"Speed = 200 (formula: {_FORMULA}) [core: {_FAIL_REASON}]",
        "core_reason": _FAIL_REASON,
    }
    violation: PropertyResultEntry = {
        "type": "property",
        "status": "fails",
        "property_index": 0,
        "timestamp": 1000,
        "reason": _FAIL_REASON,
        "enrichment": enrichment,
    }
    expected: PropertyBatchResponse = {"type": "property_batch", "results": [violation]}
    assert reply == expected
