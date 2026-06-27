# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
"""Decode-validation tightening (cross-binding lockstep, Python side).

``normalize_dbc`` / ``normalize_signal`` / ``parse_extraction_buffer`` must
reject malformed core output — out-of-range CAN ids and DLCs, out-of-range
signal bit positions, a bad ``presence`` discriminator, and trailing bytes on
the binary extraction buffer — rather than silently decoding it.  Each rejection
sets exactly one bad field on an otherwise well-formed input; the positive cases
prove well-formed input still decodes.  (Real ``formatDBC`` output is covered
end-to-end by ``test_dbc_corpus_parity`` and ``test_format_dbc``.)
"""

from __future__ import annotations

import struct
from typing import TYPE_CHECKING

import pytest

from aletheia import ProtocolError
from aletheia.client._client_bin import parse_extraction_buffer
from aletheia.client._helpers.dbc_normalize import normalize_dbc, normalize_signal

if TYPE_CHECKING:
    from aletheia.types import JSONValue


def _valid_signal() -> dict[str, JSONValue]:
    """Return a minimal well-formed (always-present) signal to mutate."""
    sig: dict[str, JSONValue] = {
        "name": "S",
        "startBit": 0,
        "length": 8,
        "presence": "always",
    }
    return sig


def _dbc_with_message(overrides: dict[str, JSONValue]) -> dict[str, JSONValue]:
    """Build a minimal well-formed DBC envelope with one message, field-overridable."""
    message: dict[str, JSONValue] = {
        "id": 0x100,
        "name": "M",
        "dlc": 8,
        "sender": "",
        "signals": [_valid_signal()],
    }
    message.update(overrides)
    dbc: dict[str, JSONValue] = {"version": "1.0", "messages": [message]}
    return dbc


class TestMessageMetaValidation:
    """CAN id range (per ``extended``) and DLC byte count."""

    def test_accepts_well_formed(self) -> None:
        """Decode a well-formed message envelope."""
        assert normalize_dbc(_dbc_with_message({}))["messages"]

    def test_rejects_standard_id_over_11_bits(self) -> None:
        """Reject a standard id above 0x7FF."""
        with pytest.raises(ProtocolError):
            normalize_dbc(_dbc_with_message({"id": 0x800}))

    def test_accepts_max_standard_id(self) -> None:
        """Accept the 0x7FF standard-frame boundary."""
        assert normalize_dbc(_dbc_with_message({"id": 0x7FF}))["messages"]

    def test_rejects_extended_id_over_29_bits(self) -> None:
        """Reject an extended id at 1<<29."""
        with pytest.raises(ProtocolError):
            normalize_dbc(_dbc_with_message({"id": 1 << 29, "extended": True}))

    def test_rejects_invalid_dlc_byte_count(self) -> None:
        """Reject a DLC of 9 bytes (not a valid CAN/CAN-FD length)."""
        with pytest.raises(ProtocolError):
            normalize_dbc(_dbc_with_message({"dlc": 9}))

    def test_accepts_canfd_dlc(self) -> None:
        """Accept the 64-byte CAN-FD maximum."""
        assert normalize_dbc(_dbc_with_message({"dlc": 64}))["messages"]


class TestSignalBitValidation:
    """Signal ``startBit`` 0-511 / ``length`` 1-64."""

    def test_rejects_start_bit_over_511(self) -> None:
        """Reject a startBit above 511."""
        sig = _valid_signal()
        sig["startBit"] = 512
        with pytest.raises(ProtocolError):
            normalize_signal(sig)

    def test_accepts_max_start_bit(self) -> None:
        """Accept the 511 boundary."""
        sig = _valid_signal()
        sig["startBit"] = 511
        assert normalize_signal(sig)["name"] == "S"

    def test_rejects_zero_length(self) -> None:
        """Reject a zero bit length."""
        sig = _valid_signal()
        sig["length"] = 0
        with pytest.raises(ProtocolError):
            normalize_signal(sig)

    def test_rejects_length_over_64(self) -> None:
        """Reject a bit length above 64."""
        sig = _valid_signal()
        sig["length"] = 65
        with pytest.raises(ProtocolError):
            normalize_signal(sig)

    def test_accepts_max_length(self) -> None:
        """Accept the 64-bit boundary."""
        sig = _valid_signal()
        sig["length"] = 64
        assert normalize_signal(sig)["name"] == "S"


class TestPresenceValidation:
    """The explicit ``presence`` discriminator."""

    def test_rejects_unknown_presence(self) -> None:
        """Reject a presence that is neither always nor multiplexed."""
        sig = _valid_signal()
        sig["presence"] = "sometimes"
        with pytest.raises(ProtocolError):
            normalize_signal(sig)

    def test_rejects_missing_presence(self) -> None:
        """Reject a signal with no presence discriminator."""
        sig = _valid_signal()
        del sig["presence"]
        with pytest.raises(ProtocolError):
            normalize_signal(sig)

    def test_rejects_multiplexed_empty_values(self) -> None:
        """Reject a multiplexed signal with an empty multiplex_values list."""
        sig = _valid_signal()
        sig["presence"] = "multiplexed"
        sig["multiplexor"] = "Mode"
        sig["multiplex_values"] = []
        with pytest.raises(ProtocolError):
            normalize_signal(sig)

    def test_rejects_multiplexed_missing_values(self) -> None:
        """Reject a multiplexed signal with no multiplex_values key."""
        sig = _valid_signal()
        sig["presence"] = "multiplexed"
        sig["multiplexor"] = "Mode"
        with pytest.raises(ProtocolError):
            normalize_signal(sig)

    def test_rejects_multiplexed_empty_multiplexor(self) -> None:
        """Reject a multiplexed signal with an empty multiplexor name."""
        sig = _valid_signal()
        sig["presence"] = "multiplexed"
        sig["multiplexor"] = ""
        sig["multiplex_values"] = [0]
        with pytest.raises(ProtocolError):
            normalize_signal(sig)

    def test_rejects_multiplex_value_over_u32(self) -> None:
        """Reject a multiplex selector value above the u32 range."""
        sig = _valid_signal()
        sig["presence"] = "multiplexed"
        sig["multiplexor"] = "Mode"
        sig["multiplex_values"] = [1 << 32]
        with pytest.raises(ProtocolError):
            normalize_signal(sig)

    def test_accepts_well_formed_multiplexed(self) -> None:
        """Accept a well-formed multiplexed signal."""
        sig = _valid_signal()
        sig["presence"] = "multiplexed"
        sig["multiplexor"] = "Mode"
        sig["multiplex_values"] = [0, 1]
        assert normalize_signal(sig)["name"] == "S"


class TestExtractionTrailingBytes:
    """``parse_extraction_buffer`` rejects trailing bytes."""

    def test_accepts_exact_buffer(self) -> None:
        """Accept a buffer consumed exactly (one value, no tail)."""
        buf = struct.pack("<HHH", 1, 0, 0) + struct.pack("<Hqq", 0, 100, 1)
        assert parse_extraction_buffer(buf, ("Speed",)).values == {"Speed": 100.0}

    def test_rejects_trailing_bytes(self) -> None:
        """Reject a buffer with a trailing byte past the computed layout."""
        buf = struct.pack("<HHH", 1, 0, 0) + struct.pack("<Hqq", 0, 100, 1)
        with pytest.raises(ProtocolError, match="trailing"):
            parse_extraction_buffer(buf + b"\x00", ("Speed",))
