# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
"""``build_frame`` / ``update_frame`` write a requested value exactly or refuse it.

The kernel refuses a value outside the signal's declared ``[minimum,
maximum]``, a value no integer raw value scales to under the signal's factor
and offset, and two requested signals sharing a bit, each with its own code;
none reaches a frame.  Every case runs through both entries.
"""

from fractions import Fraction
from pathlib import Path
from typing import Literal, NewType

import pytest
from _dbc_helpers import dbc, message, signal

from aletheia import AletheiaClient, DBCDefinition, ProtocolError
from aletheia.codes import ErrorCode
from aletheia.common_types import Prose
from aletheia.dbc import dbc_to_json
from aletheia.types import DLCCode

EntryName = Literal["build_frame", "update_frame"]
MessageId = NewType("MessageId", int)
# The first two bytes a written frame holds; the other six stay zero.
LeadBytes = NewType("LeadBytes", bytes)

# One 8-bit signal at factor 1 and one at factor 1/2, each declared over
# exactly the values its bits carry.
_VALUE_DBC = dbc(
    [
        message(
            256,
            "Msg",
            [
                signal("S", length=8, maximum=255),
                signal("H", start_bit=8, length=8, factor=Fraction(1, 2), maximum=Fraction(255, 2)),
            ],
        ),
    ]
)
_VALUE_MSG = MessageId(256)

# PayloadA (Mode 0) and PayloadB (Mode 1) both occupy bits 8 to 23.
_MUX_DBC = Path(__file__).parent / "fixtures" / "dbc_corpus" / "multiplexing.dbc"
_MUX_MSG = MessageId(100)

# Each case's request, by the case's name.
_REQUESTS = {
    Prose("above the maximum"): {"S": 256},
    Prose("below the minimum"): {"S": -1},
    Prose("between two raw values"): {"S": Fraction(3, 2)},
    Prose("between two scaled steps"): {"H": Fraction(3, 10)},
    Prose("two signals over the same bits"): {"PayloadA": 1, "PayloadB": 1},
    Prose("on the declared maximums"): {"S": 255, "H": Fraction(255, 2)},
    Prose("on the declared minimums"): {"S": 0, "H": 0},
    Prose("on a scaled step"): {"S": 7, "H": Fraction(1, 2)},
}

_ENTRIES = pytest.mark.parametrize("entry", ["build_frame", "update_frame"])


def _write(client: AletheiaClient, entry: EntryName, can_id: MessageId, case: Prose) -> bytearray:
    """Run one entry on a case's request, updating a zero frame."""
    signals = _REQUESTS[case]
    if entry == "build_frame":
        return client.build_frame(can_id=can_id, dlc=DLCCode(8), signals=signals)
    return client.update_frame(can_id=can_id, dlc=DLCCode(8), frame=bytearray(8), signals=signals)


def _refusal(
    entry: EntryName, dbc_def: DBCDefinition, can_id: MessageId, case: Prose
) -> ProtocolError:
    """Load ``dbc_def``, run the entry on the case, and return the refusal it raises."""
    with AletheiaClient() as client:
        assert client.parse_dbc(dbc_def)["status"] == "success"
        with pytest.raises(ProtocolError) as excinfo:
            _ = _write(client, entry, can_id, case)
    return excinfo.value


@_ENTRIES
@pytest.mark.parametrize(
    ("case", "code", "said"),
    [
        (
            Prose("above the maximum"),
            ErrorCode.FRAME_VALUE_OUT_OF_RANGE,
            Prose("value 256 for signal 'S' is outside [0, 255]"),
        ),
        (
            Prose("below the minimum"),
            ErrorCode.FRAME_VALUE_OUT_OF_RANGE,
            Prose("value -1 for signal 'S' is outside [0, 255]"),
        ),
        (
            Prose("between two raw values"),
            ErrorCode.FRAME_VALUE_NOT_REPRESENTABLE,
            Prose("no integer raw value scales to value 1.5 for signal 'S' (factor 1, offset 0)"),
        ),
        (
            Prose("between two scaled steps"),
            ErrorCode.FRAME_VALUE_NOT_REPRESENTABLE,
            Prose("no integer raw value scales to value 0.3 for signal 'H' (factor 0.5, offset 0)"),
        ),
    ],
)
def test_a_value_its_signal_cannot_carry_is_refused(
    entry: EntryName, case: Prose, code: ErrorCode, said: Prose
) -> None:
    """Past either bound, or between two scaled steps, refused with its code and message."""
    refusal = _refusal(entry, _VALUE_DBC, _VALUE_MSG, case)
    assert refusal.code == code
    assert str(refusal) == f"{entry} failed: {said}"


@_ENTRIES
def test_two_signals_sharing_a_bit_are_refused(entry: EntryName) -> None:
    """Two multiplexed signals over the same bits are ``frame_signals_overlap``."""
    mux = dbc_to_json(str(_MUX_DBC))
    refusal = _refusal(entry, mux, _MUX_MSG, Prose("two signals over the same bits"))
    assert refusal.code == ErrorCode.FRAME_SIGNALS_OVERLAP
    assert str(refusal) == f"{entry} failed: signals overlap"


@_ENTRIES
@pytest.mark.parametrize(
    ("case", "lead"),
    [
        (Prose("on the declared maximums"), LeadBytes(b"\xff\xff")),
        (Prose("on the declared minimums"), LeadBytes(b"\x00\x00")),
        (Prose("on a scaled step"), LeadBytes(b"\x07\x01")),
    ],
)
def test_the_declared_bounds_and_a_scaled_step_are_written_exactly(
    entry: EntryName, case: Prose, lead: LeadBytes
) -> None:
    """Values on the declared bounds and on a factor step encode, and read back, exactly."""
    with AletheiaClient() as client:
        assert client.parse_dbc(_VALUE_DBC)["status"] == "success"
        written = _write(client, entry, _VALUE_MSG, case)
        result = client.extract_signals(can_id=_VALUE_MSG, dlc=DLCCode(8), data=written)
    assert written == bytearray(lead + bytes(6))
    signals = _REQUESTS[case]
    assert {key: result.get(key) for key in signals} == signals
