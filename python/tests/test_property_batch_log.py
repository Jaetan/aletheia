# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
"""``send_frame`` logs a property batch with no failing entry as a satisfaction.

Each frame whose reply is a ``property_batch`` logs one DEBUG
``frame.processed`` record naming the frame's timestamp, identifier and
extended bit, and ``response=violation`` when an entry fails, otherwise
``response=satisfaction``.
"""

from __future__ import annotations

import logging
from typing import TYPE_CHECKING

import pytest
from _dbc_helpers import dbc, message, signal

from aletheia import AletheiaClient, Signal
from aletheia.types import DLCCode

if TYPE_CHECKING:
    from aletheia.types import PropertyBatchResponse

# ``set_properties`` renders each formula's rational threshold via the kernel,
# which needs the GHC runtime up.
pytestmark = pytest.mark.usefixtures("rts_up")

# A 29-bit id past the 11-bit range, so it names an extended message only.
_EXTENDED_ID = 0x18FF0001


def test_a_batch_of_satisfactions_logs_the_frame_as_a_satisfaction(
    caplog: pytest.LogCaptureFixture,
) -> None:
    """An Eventually met on a 29-bit frame logs that frame with ``response=satisfaction``."""
    extended_message = message(_EXTENDED_ID, "ExtMsg", [signal("Speed")])
    extended_message["extended"] = True
    with caplog.at_level(logging.DEBUG, logger="aletheia"), AletheiaClient() as client:
        client.parse_dbc(dbc([extended_message]))
        client.set_properties([Signal("Speed").greater_than(100).eventually().to_dict()])
        client.start_stream()
        reply = client.send_frame(
            1000, _EXTENDED_ID, DLCCode(8), bytes([150, 0, 0, 0, 0, 0, 0, 0]), extended=True
        )

    satisfied: PropertyBatchResponse = {
        "type": "property_batch",
        "results": [{"type": "property", "status": "holds", "property_index": 0}],
    }
    assert reply == satisfied
    assert [
        (record.levelno, record.getMessage())
        for record in caplog.records
        if record.getMessage().startswith("frame.processed")
    ] == [
        (
            logging.DEBUG,
            "frame.processed ts=1000 canId=419364865 extended=true response=satisfaction",
        )
    ]
