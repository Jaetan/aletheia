# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
"""Tests for the Agda validator's checks on where a signal sits in its message's frame.

Tests that validateDBC detects a signal past the DLC, overlapping signals,
zero and excessive bit lengths, a start bit past the frame and a message
with no signals.
"""

from typing import cast

import pytest
from _validator_helpers import (
    make_dbc,
    make_message,
    make_mux_signal,
    make_signal,
    single_message_dbc,
)

from aletheia import AletheiaClient, ProtocolError


class TestSignalExceedsDLC:
    """Check 8: Signal bit range must fit within DLC × 8 bits."""

    def test_little_endian_signal_exceeds_dlc(self) -> None:
        """Verify little endian signal exceeds dlc."""
        dbc = single_message_dbc(
            [
                make_signal("TooWide", start_bit=56, length=16, byte_order="little_endian"),
            ],
            dlc=8,
        )
        with AletheiaClient() as client:
            result = client.validate_dbc(dbc)

        codes = [i["code"] for i in result["issues"]]
        assert "signal_exceeds_dlc" in codes

    def test_little_endian_signal_fits_dlc(self) -> None:
        """Verify little endian signal fits dlc."""
        dbc = single_message_dbc(
            [
                make_signal("Fits", start_bit=0, length=16, byte_order="little_endian"),
            ],
            dlc=8,
        )
        with AletheiaClient() as client:
            result = client.validate_dbc(dbc)

        exceeds = [i for i in result["issues"] if i["code"] == "signal_exceeds_dlc"]
        assert exceeds == []

    def test_big_endian_signal_exceeds_dlc(self) -> None:
        # Out-of-capacity geometry is refused by the shared entry gate
        # (`geometryRefusal`) before the validator runs; the typed error
        # names the SUBMITTED values.  A length wider than the whole
        # frame draws `parse_signal_bit_length_exceeds_frame` here
        # instead of the downstream validator's signal_exceeds_dlc.
        """Verify big endian signal exceeds dlc."""
        dbc = single_message_dbc(
            [
                make_signal(
                    "TooWide",
                    start_bit=7,
                    length=33,
                    byte_order="big_endian",
                    maximum=255,
                ),
            ],
            dlc=4,
        )
        with (
            AletheiaClient() as client,
            pytest.raises(ProtocolError, match="bit length 33 exceeds the frame capacity"),
        ):
            client.validate_dbc(dbc)

    @pytest.mark.parametrize("field", ["startBit", "length"])
    def test_negative_geometry_field_refused_truthfully(self, field: str) -> None:
        """A negative geometry value draws the strict non-natural refusal.

        The kernel's strict natural-number lookup distinguishes a present
        non-natural value from an absent field, so a negative ``startBit``
        or ``length`` is refused as ``parse_non_natural_field`` naming the
        offending field — never absorbed by a clamp or misreported as a
        missing field.
        """
        dbc = single_message_dbc([make_signal("Neg", start_bit=0, length=8)])
        signal = cast("dict[str, object]", dbc["messages"][0]["signals"][0])
        signal[field] = -1
        with (
            AletheiaClient() as client,
            pytest.raises(
                ProtocolError,
                match=f"field '{field}' must be a JSON natural number",
            ),
        ):
            client.validate_dbc(dbc)

    def test_big_endian_signal_fits_dlc(self) -> None:
        # BitsInFrame checks startBit + bitLength ≤ dlc * 8 on the
        # CONVERTED start bit. convertStartBit uses actual DLC.
        # startBit=7, length=8, dlc=4 → physBit=31, converted=24,
        # 24+8=32 ≤ 4*8=32 → fits
        """Verify big endian signal fits dlc."""
        dbc = single_message_dbc(
            [
                make_signal("Fits", start_bit=7, length=8, byte_order="big_endian", maximum=255),
            ],
            dlc=4,
        )
        with AletheiaClient() as client:
            result = client.validate_dbc(dbc)

        exceeds = [i for i in result["issues"] if i["code"] == "signal_exceeds_dlc"]
        assert exceeds == []

    def test_small_dlc_catches_overflow(self) -> None:
        # DLC=2 means only 16 bits; an in-gate signal (start bit 12 < 16,
        # length 8 ≤ 16) whose extent still runs past the frame keeps the
        # validator's CHECK 8 arm live (a start bit at/past 16 would be
        # refused earlier by the entry gate with a typed parse error).
        """Verify small dlc catches overflow."""
        dbc = single_message_dbc(
            [
                make_signal("Overflow", start_bit=12, length=8, byte_order="little_endian"),
            ],
            dlc=2,
        )
        with AletheiaClient() as client:
            result = client.validate_dbc(dbc)

        codes = [i["code"] for i in result["issues"]]
        assert "signal_exceeds_dlc" in codes


class TestSignalOverlap:
    """Check 9: Non-multiplexed coexisting signals must not share bits."""

    def test_overlapping_signals_detected(self) -> None:
        """Verify overlapping signals detected."""
        dbc = single_message_dbc(
            [
                make_signal("Sig1", start_bit=0, length=16),
                make_signal("Sig2", start_bit=8, length=16),
            ]
        )
        with AletheiaClient() as client:
            result = client.validate_dbc(dbc)

        codes = [i["code"] for i in result["issues"]]
        assert "signal_overlap" in codes

    def test_non_overlapping_signals_ok(self) -> None:
        """Verify non overlapping signals ok."""
        dbc = single_message_dbc(
            [
                make_signal("Sig1", start_bit=0, length=8),
                make_signal("Sig2", start_bit=8, length=8),
            ]
        )
        with AletheiaClient() as client:
            result = client.validate_dbc(dbc)

        overlaps = [i for i in result["issues"] if i["code"] == "signal_overlap"]
        assert overlaps == []

    def test_multiplexed_signals_can_share_bits(self) -> None:
        """Multiplexed signals that can't coexist should not report overlap."""
        dbc = single_message_dbc(
            [
                make_signal("Mux", start_bit=0, length=8),
                make_mux_signal("A", "Mux", 0, start_bit=8, length=8),
                make_mux_signal("B", "Mux", 1, start_bit=8, length=8),
            ]
        )
        with AletheiaClient() as client:
            result = client.validate_dbc(dbc)

        overlaps = [i for i in result["issues"] if i["code"] == "signal_overlap"]
        assert overlaps == []


class TestBitLengthZero:
    """Check 10: Signal bit length must not be zero.

    Both byte orders are refused at the shared entry gate (its
    positive-length condition) with ``parse_signal_bit_length_zero``.
    The validator check stays as defense-in-depth but is proven
    unreachable from the public parse routes (``GeometryGateDeadness``).
    """

    def test_zero_length_le_rejected_at_parse(self) -> None:
        """LE bitLength=0 surfaces parse_signal_bit_length_zero from validate_dbc."""
        dbc = single_message_dbc(
            [
                make_signal("ZeroLen", length=0, byte_order="little_endian"),
            ]
        )
        with AletheiaClient() as client, pytest.raises(ProtocolError, match="bit length"):
            client.validate_dbc(dbc)

    def test_zero_length_be_rejected_at_parse(self) -> None:
        """BE bitLength=0 surfaces parse_signal_bit_length_zero from validate_dbc."""
        dbc = single_message_dbc(
            [
                make_signal("ZeroLen", length=0, byte_order="big_endian"),
            ]
        )
        with AletheiaClient() as client, pytest.raises(ProtocolError, match="bit length"):
            client.validate_dbc(dbc)

    def test_nonzero_length_ok(self) -> None:
        """Verify nonzero length ok."""
        dbc = single_message_dbc(
            [
                make_signal("Normal", length=8),
            ]
        )
        with AletheiaClient() as client:
            result = client.validate_dbc(dbc)

        zero_issues = [i for i in result["issues"] if i["code"] == "bit_length_zero"]
        assert zero_issues == []


class TestEmptyMessage:
    """Check 14: Message with no signals."""

    def test_empty_message_warned(self) -> None:
        """Verify empty message warned."""
        dbc = make_dbc(
            [
                make_message(0x100, "Empty", []),
            ]
        )
        with AletheiaClient() as client:
            result = client.validate_dbc(dbc)

        codes = [i["code"] for i in result["issues"]]
        assert "empty_message" in codes
        # Should be warning, not error
        empty_issues = [i for i in result["issues"] if i["code"] == "empty_message"]
        assert all(i["severity"] == "warning" for i in empty_issues)

    def test_message_with_signals_ok(self) -> None:
        """Verify message with signals ok."""
        dbc = make_dbc(
            [
                make_message(0x100, "HasSigs", [make_signal("Sig1")]),
            ]
        )
        with AletheiaClient() as client:
            result = client.validate_dbc(dbc)

        empty_issues = [i for i in result["issues"] if i["code"] == "empty_message"]
        assert empty_issues == []


class TestStartBitOutOfRange:
    """Check 15: start bit at/past the containing message's frame capacity.

    The shared entry gate refuses such geometry with a typed parse error
    before the validator runs (proven dead on the public routes by
    ``GeometryGateDeadness``), so these tests pin the non-firing side:
    an in-frame start bit never draws the issue.
    """

    def test_start_bit_63_ok(self) -> None:
        """Verify start bit 63 ok."""
        dbc = single_message_dbc(
            [
                make_signal("OkStart", start_bit=63, length=1, maximum=1),
            ]
        )
        with AletheiaClient() as client:
            result = client.validate_dbc(dbc)

        sb_issues = [i for i in result["issues"] if i["code"] == "start_bit_out_of_range"]
        assert sb_issues == []

    def test_start_bit_0_ok(self) -> None:
        """Verify start bit 0 ok."""
        dbc = single_message_dbc(
            [
                make_signal("OkStart", start_bit=0, length=8),
            ]
        )
        with AletheiaClient() as client:
            result = client.validate_dbc(dbc)

        sb_issues = [i for i in result["issues"] if i["code"] == "start_bit_out_of_range"]
        assert sb_issues == []


class TestBitLengthExcessive:
    """Check 16: bit length exceeding the containing message's frame capacity.

    The shared entry gate refuses such geometry with a typed parse error
    before the validator runs (proven dead on the public routes by
    ``GeometryGateDeadness``), so these tests pin the non-firing side:
    an in-frame bit length never draws the issue.
    """

    def test_bit_length_32_ok(self) -> None:
        # A 32-bit signal fits the default 8-byte frame with room to spare.
        """Verify bit length 32 ok."""
        dbc = single_message_dbc(
            [
                make_signal("Counter", start_bit=0, length=32, maximum=4294967295),
            ]
        )
        with AletheiaClient() as client:
            result = client.validate_dbc(dbc)

        bl_issues = [i for i in result["issues"] if i["code"] == "bit_length_excessive"]
        assert bl_issues == []

    def test_bit_length_1_ok(self) -> None:
        """Verify bit length 1 ok."""
        dbc = single_message_dbc(
            [
                make_signal("OneBit", start_bit=0, length=1, maximum=1),
            ]
        )
        with AletheiaClient() as client:
            result = client.validate_dbc(dbc)

        bl_issues = [i for i in result["issues"] if i["code"] == "bit_length_excessive"]
        assert bl_issues == []
