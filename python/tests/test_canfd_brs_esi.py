# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
"""Unit tests for CAN-FD BRS / ESI metadata plumbing on the Python side.

R19 Phase 2 cluster 18 — AGDA-D-10.1 / 13.1 / 17.1 closure.

The Aletheia kernel does not consume BRS / ESI (LTL atomic-predicate
scope is signal-level per ``Aletheia.Trace.CANTrace`` design comment);
these bits are pass-through metadata threaded from the binding through
the C FFI for downstream consumers.

This file covers the binding's structural plumbing — the encoding
helper, the ``CANFrameTuple`` shape, and the python-can lift in
``can_log.convert_message``.  End-to-end FFI round-trip lives in
``test_unified_client_canfd_mux.py`` so the real library has to
accept the new 11-arg ``aletheia_send_frame`` signature.
"""

from __future__ import annotations

import can

from aletheia import CANFrameTuple
from aletheia.can_log import convert_message
from aletheia.client._types import encode_maybe_bool
from aletheia.types import DLCCode


class TestEncodeMaybeBool:
    """``encode_maybe_bool`` mirrors the Haskell shim's ``mkMaybeBool``."""

    def test_none_encodes_to_zero_zero(self) -> None:
        """``None`` lifts to the absent (present=0, value=0) byte pair."""
        assert encode_maybe_bool(b=None) == (0, 0)

    def test_true_encodes_to_one_one(self) -> None:
        """``True`` lifts to present=1, value=1."""
        assert encode_maybe_bool(b=True) == (1, 1)

    def test_false_encodes_to_one_zero(self) -> None:
        """``False`` lifts to present=1, value=0."""
        assert encode_maybe_bool(b=False) == (1, 0)


class TestCANFrameTupleBrsEsi:
    """``CANFrameTuple`` carries ``brs`` / ``esi`` with ``None`` defaults."""

    def test_default_brs_esi_is_none(self) -> None:
        """5-positional construction defaults BRS / ESI to None."""
        frame = CANFrameTuple(1000, 0x100, DLCCode(8), bytearray(8), extended=False)
        assert frame.brs is None
        assert frame.esi is None

    def test_explicit_brs_esi(self) -> None:
        """Verify BRS=True, ESI=False round-trip through the NamedTuple."""
        frame = CANFrameTuple(
            1000,
            0x100,
            DLCCode(8),
            bytearray(8),
            extended=False,
            brs=True,
            esi=False,
        )
        assert frame.brs is True
        assert frame.esi is False


class TestConvertMessageBrsEsi:
    """``can_log.convert_message`` populates BRS / ESI iff ``is_fd``."""

    @staticmethod
    def _make_msg(**overrides: object) -> can.Message:
        """Build a ``can.Message`` mirroring the ``test_can_log`` fixture shape."""
        msg = can.Message()
        msg.timestamp = 1.0
        msg.arbitration_id = 0x100
        msg.data = bytearray(8)
        msg.dlc = 8
        msg.is_error_frame = False
        msg.is_remote_frame = False
        msg.is_extended_id = False
        msg.is_fd = False
        msg.bitrate_switch = False
        msg.error_state_indicator = False
        for k, v in overrides.items():
            setattr(msg, k, v)
        return msg

    def test_can_2_0b_yields_none_brs_esi(self) -> None:
        """A non-FD frame surfaces None for both bits.

        The bit doesn't exist on the wire for classical CAN, so any
        python-can default (typically ``False``) must not be passed through.
        """
        result = convert_message(
            self._make_msg(),
            skip_error_frames=True,
            skip_remote_frames=True,
        )
        assert result is not None
        assert result.brs is None
        assert result.esi is None

    def test_can_fd_lifts_bitrate_switch(self) -> None:
        """A CAN-FD frame with BRS set surfaces ``brs=True``."""
        result = convert_message(
            self._make_msg(is_fd=True, bitrate_switch=True, error_state_indicator=False),
            skip_error_frames=True,
            skip_remote_frames=True,
        )
        assert result is not None
        assert result.brs is True
        assert result.esi is False

    def test_can_fd_lifts_error_state_indicator(self) -> None:
        """A CAN-FD frame with ESI set surfaces ``esi=True``."""
        result = convert_message(
            self._make_msg(is_fd=True, bitrate_switch=False, error_state_indicator=True),
            skip_error_frames=True,
            skip_remote_frames=True,
        )
        assert result is not None
        assert result.brs is False
        assert result.esi is True
