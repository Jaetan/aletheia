"""Single source of the canonical DBC fixture used across tests.

The ``CANONICAL_DBC`` dict is the shared input for the cross-binding
integration test, the hypothesis property tests, and the conftest
``simple_dbc`` / ``sample_dbc`` fixtures.  Pulling them all from this
module lets each test site reference the same DBC content without
copy-pasting the TypedDict literal (pylint cat 6 R0801 — duplicate-code).
"""

from __future__ import annotations

from fractions import Fraction
from typing import TYPE_CHECKING

from aletheia._dbc_types import empty_dbc_tier2
from aletheia.protocols import DLCByteCount

if TYPE_CHECKING:
    from aletheia.protocols import DBCDefinition, DBCMessage, DBCSignalAlways

CANONICAL_SIGNAL: DBCSignalAlways = {
    "name": "TestSignal",
    "startBit": 0,
    "length": 16,
    "byteOrder": "little_endian",
    "signed": False,
    "factor": Fraction(1),
    "offset": Fraction(0),
    "minimum": Fraction(0),
    "maximum": Fraction(65535),
    "unit": "",
    "presence": "always",
}


def make_dbc(*, msg_id: int = 256, sender: str = "ECU") -> DBCDefinition:
    """Build a minimal DBC from the canonical signal with overridable metadata.

    Two existing fixtures need slightly different message metadata:
    ``simple_dbc`` uses ``id=256, sender="ECU"`` (cross-binding default);
    ``sample_dbc`` uses ``id=0x100, sender="TestECU"`` (legacy fixture).
    Both pull the same signal body from ``CANONICAL_SIGNAL``.
    """
    msg: DBCMessage = {
        "id": msg_id,
        "name": "TestMessage",
        "dlc": DLCByteCount(8),
        "sender": sender,
        "signals": [CANONICAL_SIGNAL],
    }
    return {
        "version": "1.0",
        "messages": [msg],
        **empty_dbc_tier2(),
    }


CANONICAL_DBC: DBCDefinition = make_dbc()
