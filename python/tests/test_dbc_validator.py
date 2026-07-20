# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
"""Tests for DBC validation via the Agda validator.

Tests that the Aletheia engine's validateDBC command correctly detects
structural issues in DBC definitions (duplicate IDs, duplicate signal
names, factor zero, multiplexor issues, global name collisions,
min > max).
"""

from fractions import Fraction
from typing import TYPE_CHECKING, Unpack, cast

import pytest
from _dbc_helpers import SignalOverrides, mux_signal
from _dbc_helpers import dbc as _build_dbc
from _dbc_helpers import message as _build_msg
from _dbc_helpers import signal as _build_sig

from aletheia import AletheiaClient, DBCDefinition, ProtocolError

if TYPE_CHECKING:
    from aletheia.types import (
        Command,
        DBCMessage,
        DBCSignal,
        DBCSignalMultiplexed,
        Response,
    )

# Validator tests default to 8-bit signals ranged 0..255, matching the
# narrow signals most DBC structural-validation cases exercise.
_VALIDATOR_DEFAULTS: SignalOverrides = {"length": 8, "maximum": 255}


def _make_dbc(messages: list[DBCMessage]) -> DBCDefinition:
    """Build a minimal DBC with given messages."""
    return _build_dbc(messages)


def _make_message(
    msg_id: int,
    name: str,
    signals: list[DBCSignal] | None = None,
    *,
    dlc: int = 8,
    sender: str = "ECU",
) -> DBCMessage:
    """Build a DBC message."""
    return _build_msg(msg_id, name, signals or [], dlc=dlc, sender=sender)


def _make_signal(name: str, **overrides: Unpack[SignalOverrides]) -> DBCSignal:
    """Build an 8-bit byte-aligned signal with validator-friendly defaults."""
    merged: SignalOverrides = {**_VALIDATOR_DEFAULTS, **overrides}
    return _build_sig(name, **merged)


def _make_mux_signal(
    name: str,
    multiplexor: str,
    mux_value: int,
    *,
    start_bit: int = 0,
    length: int = 8,
) -> DBCSignalMultiplexed:
    """Build a multiplexed DBC signal."""
    return mux_signal(name, multiplexor, [mux_value], start_bit=start_bit, length=length)


class TestValidDBCPassesClean:
    """Tests that valid DBCs produce no issues."""

    def test_valid_single_message(self) -> None:
        """Verify valid single message."""
        dbc = _make_dbc(
            [
                _make_message(
                    0x100,
                    "Msg1",
                    [
                        _make_signal("Speed", start_bit=0, length=16, maximum=65535),
                        _make_signal("RPM", start_bit=16, length=16, maximum=65535),
                    ],
                ),
            ]
        )
        with AletheiaClient() as client:
            result = client.validate_dbc(dbc)

        assert result["status"] == "validation"
        assert result["has_errors"] is False
        assert result["issues"] == []

    def test_valid_multiple_messages(self) -> None:
        """Verify valid multiple messages."""
        dbc = _make_dbc(
            [
                _make_message(
                    0x100,
                    "Engine",
                    [
                        _make_signal("Speed", start_bit=0, length=16, maximum=65535),
                    ],
                ),
                _make_message(
                    0x200,
                    "Brakes",
                    [
                        _make_signal("BrakePressure", start_bit=0, length=8),
                    ],
                ),
            ]
        )
        with AletheiaClient() as client:
            result = client.validate_dbc(dbc)

        assert result["has_errors"] is False
        assert result["issues"] == []


class TestDuplicateMessageId:
    """Check 1: Duplicate message IDs across the DBC."""

    def test_duplicate_message_id_detected(self) -> None:
        """Verify duplicate message id detected."""
        dbc = _make_dbc(
            [
                _make_message(0x100, "Msg1", [_make_signal("Sig1")]),
                _make_message(0x100, "Msg2", [_make_signal("Sig2")]),
            ]
        )
        with AletheiaClient() as client:
            result = client.validate_dbc(dbc)

        assert result["has_errors"] is True
        codes = [i["code"] for i in result["issues"]]
        assert "duplicate_message_id" in codes

    def test_different_ids_no_duplicate(self) -> None:
        """Verify different ids no duplicate."""
        dbc = _make_dbc(
            [
                _make_message(0x100, "Msg1", [_make_signal("Sig1")]),
                _make_message(0x200, "Msg2", [_make_signal("Sig2")]),
            ]
        )
        with AletheiaClient() as client:
            result = client.validate_dbc(dbc)

        dup_codes = [i for i in result["issues"] if i["code"] == "duplicate_message_id"]
        assert dup_codes == []


# Check 2: Duplicate signal names within a single message.


def test_duplicate_signal_name_detected() -> None:
    """Verify duplicate signal name detected."""
    dbc = _make_dbc(
        [
            _make_message(
                0x100,
                "Msg1",
                [
                    _make_signal("Speed", start_bit=0, length=8),
                    _make_signal("Speed", start_bit=8, length=8),
                ],
            ),
        ]
    )
    with AletheiaClient() as client:
        result = client.validate_dbc(dbc)

    assert result["has_errors"] is True
    codes = [i["code"] for i in result["issues"]]
    assert "duplicate_signal_name" in codes


class TestFactorZero:
    """Check 3: Signal factor must not be zero."""

    def test_factor_zero_detected(self) -> None:
        """Verify factor zero detected."""
        dbc = _make_dbc(
            [
                _make_message(
                    0x100,
                    "Msg1",
                    [
                        _make_signal("BadSignal", factor=0),
                    ],
                ),
            ]
        )
        with AletheiaClient() as client:
            result = client.validate_dbc(dbc)

        assert result["has_errors"] is True
        codes = [i["code"] for i in result["issues"]]
        assert "factor_zero" in codes

    def test_nonzero_factor_ok(self) -> None:
        """Verify nonzero factor ok."""
        dbc = _make_dbc(
            [
                _make_message(
                    0x100,
                    "Msg1",
                    [
                        _make_signal("GoodSignal", factor=Fraction("0.01")),
                    ],
                ),
            ]
        )
        with AletheiaClient() as client:
            result = client.validate_dbc(dbc)

        factor_issues = [i for i in result["issues"] if i["code"] == "factor_zero"]
        assert factor_issues == []


# Check 7: Signal minimum must not exceed maximum.


def test_min_exceeds_max_detected() -> None:
    """Verify min exceeds max detected."""
    dbc = _make_dbc(
        [
            _make_message(
                0x100,
                "Msg1",
                [
                    _make_signal("BadRange", minimum=100, maximum=50),
                ],
            ),
        ]
    )
    with AletheiaClient() as client:
        result = client.validate_dbc(dbc)

    # min_exceeds_max is a warning, not an error
    assert result["has_errors"] is False
    codes = [i["code"] for i in result["issues"]]
    assert "min_exceeds_max" in codes


# Check 6: Signal names must be globally unique across all messages.


def test_global_name_collision_detected() -> None:
    """Verify global name collision detected."""
    dbc = _make_dbc(
        [
            _make_message(
                0x100,
                "Msg1",
                [
                    _make_signal("SharedName", start_bit=0, length=8),
                ],
            ),
            _make_message(
                0x200,
                "Msg2",
                [
                    _make_signal("SharedName", start_bit=0, length=8),
                ],
            ),
        ]
    )
    with AletheiaClient() as client:
        result = client.validate_dbc(dbc)

    codes = [i["code"] for i in result["issues"]]
    assert "global_name_collision" in codes


class TestSignalExceedsDLC:
    """Check 8: Signal bit range must fit within DLC × 8 bits."""

    def test_little_endian_signal_exceeds_dlc(self) -> None:
        """Verify little endian signal exceeds dlc."""
        dbc = _make_dbc(
            [
                _make_message(
                    0x100,
                    "Msg1",
                    [
                        _make_signal(
                            "TooWide", start_bit=56, length=16, byte_order="little_endian"
                        ),
                    ],
                    dlc=8,
                ),
            ]
        )
        with AletheiaClient() as client:
            result = client.validate_dbc(dbc)

        codes = [i["code"] for i in result["issues"]]
        assert "signal_exceeds_dlc" in codes

    def test_little_endian_signal_fits_dlc(self) -> None:
        """Verify little endian signal fits dlc."""
        dbc = _make_dbc(
            [
                _make_message(
                    0x100,
                    "Msg1",
                    [
                        _make_signal("Fits", start_bit=0, length=16, byte_order="little_endian"),
                    ],
                    dlc=8,
                ),
            ]
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
        dbc = _make_dbc(
            [
                _make_message(
                    0x100,
                    "Msg1",
                    [
                        _make_signal(
                            "TooWide",
                            start_bit=7,
                            length=33,
                            byte_order="big_endian",
                            maximum=255,
                        ),
                    ],
                    dlc=4,
                ),
            ]
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
        dbc = _make_dbc(
            [
                _make_message(
                    0x100,
                    "Msg1",
                    [_make_signal("Neg", start_bit=0, length=8)],
                ),
            ]
        )
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
        dbc = _make_dbc(
            [
                _make_message(
                    0x100,
                    "Msg1",
                    [
                        _make_signal(
                            "Fits", start_bit=7, length=8, byte_order="big_endian", maximum=255
                        ),
                    ],
                    dlc=4,
                ),
            ]
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
        dbc = _make_dbc(
            [
                _make_message(
                    0x100,
                    "Msg1",
                    [
                        _make_signal(
                            "Overflow", start_bit=12, length=8, byte_order="little_endian"
                        ),
                    ],
                    dlc=2,
                ),
            ]
        )
        with AletheiaClient() as client:
            result = client.validate_dbc(dbc)

        codes = [i["code"] for i in result["issues"]]
        assert "signal_exceeds_dlc" in codes


class TestSignalOverlap:
    """Check 9: Non-multiplexed coexisting signals must not share bits."""

    def test_overlapping_signals_detected(self) -> None:
        """Verify overlapping signals detected."""
        dbc = _make_dbc(
            [
                _make_message(
                    0x100,
                    "Msg1",
                    [
                        _make_signal("Sig1", start_bit=0, length=16),
                        _make_signal("Sig2", start_bit=8, length=16),
                    ],
                ),
            ]
        )
        with AletheiaClient() as client:
            result = client.validate_dbc(dbc)

        codes = [i["code"] for i in result["issues"]]
        assert "signal_overlap" in codes

    def test_non_overlapping_signals_ok(self) -> None:
        """Verify non overlapping signals ok."""
        dbc = _make_dbc(
            [
                _make_message(
                    0x100,
                    "Msg1",
                    [
                        _make_signal("Sig1", start_bit=0, length=8),
                        _make_signal("Sig2", start_bit=8, length=8),
                    ],
                ),
            ]
        )
        with AletheiaClient() as client:
            result = client.validate_dbc(dbc)

        overlaps = [i for i in result["issues"] if i["code"] == "signal_overlap"]
        assert overlaps == []

    def test_multiplexed_signals_can_share_bits(self) -> None:
        """Multiplexed signals that can't coexist should not report overlap."""
        dbc = _make_dbc(
            [
                _make_message(
                    0x100,
                    "Msg1",
                    [
                        _make_signal("Mux", start_bit=0, length=8),
                        _make_mux_signal("A", "Mux", 0, start_bit=8, length=8),
                        _make_mux_signal("B", "Mux", 1, start_bit=8, length=8),
                    ],
                ),
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
        dbc = _make_dbc(
            [
                _make_message(
                    0x100,
                    "Msg1",
                    [
                        _make_signal("ZeroLen", length=0, byte_order="little_endian"),
                    ],
                ),
            ]
        )
        with AletheiaClient() as client, pytest.raises(ProtocolError, match="bit length"):
            client.validate_dbc(dbc)

    def test_zero_length_be_rejected_at_parse(self) -> None:
        """BE bitLength=0 surfaces parse_signal_bit_length_zero from validate_dbc."""
        dbc = _make_dbc(
            [
                _make_message(
                    0x100,
                    "Msg1",
                    [
                        _make_signal("ZeroLen", length=0, byte_order="big_endian"),
                    ],
                ),
            ]
        )
        with AletheiaClient() as client, pytest.raises(ProtocolError, match="bit length"):
            client.validate_dbc(dbc)

    def test_nonzero_length_ok(self) -> None:
        """Verify nonzero length ok."""
        dbc = _make_dbc(
            [
                _make_message(
                    0x100,
                    "Msg1",
                    [
                        _make_signal("Normal", length=8),
                    ],
                ),
            ]
        )
        with AletheiaClient() as client:
            result = client.validate_dbc(dbc)

        zero_issues = [i for i in result["issues"] if i["code"] == "bit_length_zero"]
        assert zero_issues == []


class TestNonIntegerMultiplexValue:
    """Non-integer in ``multiplex_values`` is rejected with a typed wire code.

    The kernel emits ``parse_non_integer_multiplex_value`` (distinct from the
    earlier ``parse_invalid_presence`` wire code, which conflated "presence
    string not 'always'" with "non-natural element in multiplex_values").
    Both ``InvalidPresence "non-integer in multiplex_values"`` sites at
    ``JSONParser.parseNatList[⁺]`` now route to the dedicated code.

    Goes through ``validate_dbc``, which propagates the wire ``code`` field
    onto the raised ``ProtocolError`` (parallel to ``format_dbc`` /
    ``format_dbc_text``).
    """

    def test_float_in_multiplex_values_rejected(self) -> None:
        """Float in multiplex_values surfaces parse_non_integer_multiplex_value."""
        sig = _make_mux_signal("Mode", "Mux", 0, start_bit=0, length=8)
        # Adversarial: a float is not a valid JSON natural; the parser must reject.
        sig["multiplex_values"] = cast("list[int]", [1.5])
        dbc = _make_dbc([_make_message(0x100, "Msg1", [sig])])
        with AletheiaClient() as client, pytest.raises(ProtocolError) as excinfo:
            client.validate_dbc(dbc)
        assert excinfo.value.code == "parse_non_integer_multiplex_value"

    def test_string_in_multiplex_values_rejected(self) -> None:
        """Non-numeric in multiplex_values also surfaces the same typed code."""
        sig = _make_mux_signal("Mode", "Mux", 0, start_bit=0, length=8)
        # Adversarial: a non-numeric element is not a valid JSON natural.
        sig["multiplex_values"] = cast("list[int]", ["not_a_number"])
        dbc = _make_dbc([_make_message(0x100, "Msg1", [sig])])
        with AletheiaClient() as client, pytest.raises(ProtocolError) as excinfo:
            client.validate_dbc(dbc)
        assert excinfo.value.code == "parse_non_integer_multiplex_value"


class TestDuplicateMessageName:
    """Check 11: Duplicate message names across the DBC."""

    def test_duplicate_name_detected(self) -> None:
        """Verify duplicate name detected."""
        dbc = _make_dbc(
            [
                _make_message(0x100, "SameName", [_make_signal("Sig1")]),
                _make_message(0x200, "SameName", [_make_signal("Sig2")]),
            ]
        )
        with AletheiaClient() as client:
            result = client.validate_dbc(dbc)

        codes = [i["code"] for i in result["issues"]]
        assert "duplicate_message_name" in codes

    def test_different_names_ok(self) -> None:
        """Verify different names ok."""
        dbc = _make_dbc(
            [
                _make_message(0x100, "Msg1", [_make_signal("Sig1")]),
                _make_message(0x200, "Msg2", [_make_signal("Sig2")]),
            ]
        )
        with AletheiaClient() as client:
            result = client.validate_dbc(dbc)

        dup_names = [i for i in result["issues"] if i["code"] == "duplicate_message_name"]
        assert dup_names == []


class TestOffsetScaleRange:
    """Check 13: Declared [min,max] must contain the physical range.

    Physical = raw × factor + offset.
    Unsigned n-bit: raw ∈ [0, 2^n − 1].
    Signed   n-bit: raw ∈ [−2^(n−1), 2^(n−1) − 1].
    If factor < 0, the physical range inverts.
    """

    def test_unsigned_correct_range_clean(self) -> None:
        # 8-bit unsigned, factor=1, offset=0 → phys ∈ [0, 255]
        """Verify unsigned correct range clean."""
        dbc = _make_dbc(
            [
                _make_message(
                    0x100,
                    "Msg1",
                    [
                        _make_signal("Good", length=8, factor=1, offset=0, minimum=0, maximum=255),
                    ],
                ),
            ]
        )
        with AletheiaClient() as client:
            result = client.validate_dbc(dbc)

        osr = [i for i in result["issues"] if i["code"] == "offset_scale_range"]
        assert osr == []

    def test_unsigned_declared_max_too_narrow(self) -> None:
        # 8-bit unsigned, factor=1, offset=0 → phys_max=255, but declared max=200
        """Verify unsigned declared max too narrow."""
        dbc = _make_dbc(
            [
                _make_message(
                    0x100,
                    "Msg1",
                    [
                        _make_signal(
                            "Narrow", length=8, factor=1, offset=0, minimum=0, maximum=200
                        ),
                    ],
                ),
            ]
        )
        with AletheiaClient() as client:
            result = client.validate_dbc(dbc)

        osr = [i for i in result["issues"] if i["code"] == "offset_scale_range"]
        assert len(osr) == 1
        assert "maximum" in osr[0]["detail"]

    def test_signed_correct_range_clean(self) -> None:
        # 8-bit signed, factor=1, offset=0 → phys ∈ [-128, 127]
        """Verify signed correct range clean."""
        dbc = _make_dbc(
            [
                _make_message(
                    0x100,
                    "Msg1",
                    [
                        _make_signal(
                            "Temp",
                            length=8,
                            signed=True,
                            factor=1,
                            offset=0,
                            minimum=-128,
                            maximum=127,
                        ),
                    ],
                ),
            ]
        )
        with AletheiaClient() as client:
            result = client.validate_dbc(dbc)

        osr = [i for i in result["issues"] if i["code"] == "offset_scale_range"]
        assert osr == []

    def test_signed_declared_min_too_narrow(self) -> None:
        # 8-bit signed, factor=1, offset=0 → phys_min=-128, but declared min=-100
        # Declared range [-100, 127] is NARROWER than physical [-128, 127]
        # Hardware can produce values in [-128, -101] outside declared range → warning
        """Verify signed declared min too narrow."""
        dbc = _make_dbc(
            [
                _make_message(
                    0x100,
                    "Msg1",
                    [
                        _make_signal(
                            "Cold",
                            length=8,
                            signed=True,
                            factor=1,
                            offset=0,
                            minimum=-100,
                            maximum=127,
                        ),
                    ],
                ),
            ]
        )
        with AletheiaClient() as client:
            result = client.validate_dbc(dbc)

        osr = [i for i in result["issues"] if i["code"] == "offset_scale_range"]
        assert len(osr) == 1
        assert "minimum" in osr[0]["detail"]

    def test_negative_factor_unsigned(self) -> None:
        # 8-bit unsigned, factor=Fraction("-0.1"), offset=Fraction("25.5")
        # phys_min = 255 * (-0.1) + 25.5 = 0.0, phys_max = 0 * (-0.1) + 25.5 = 25.5
        """Verify negative factor unsigned."""
        dbc = _make_dbc(
            [
                _make_message(
                    0x100,
                    "Msg1",
                    [
                        _make_signal(
                            "Inverted",
                            length=8,
                            factor=Fraction("-0.1"),
                            offset=Fraction("25.5"),
                            minimum=0,
                            maximum=Fraction("25.5"),
                        ),
                    ],
                ),
            ]
        )
        with AletheiaClient() as client:
            result = client.validate_dbc(dbc)

        osr = [i for i in result["issues"] if i["code"] == "offset_scale_range"]
        assert osr == []

    def test_negative_factor_wrong_range_warns(self) -> None:
        # 8-bit unsigned, factor=Fraction("-0.1"), offset=Fraction("25.5")
        # phys range: [0.0, 25.5] (factor negative flips raw→phys direction)
        # Declared min=5.0 is ABOVE physMin=0.0 → hardware can produce [0, 5) outside declared range
        """Verify negative factor wrong range warns."""
        dbc = _make_dbc(
            [
                _make_message(
                    0x100,
                    "Msg1",
                    [
                        _make_signal(
                            "Bad",
                            length=8,
                            factor=Fraction("-0.1"),
                            offset=Fraction("25.5"),
                            minimum=5,
                            maximum=Fraction("25.5"),
                        ),
                    ],
                ),
            ]
        )
        with AletheiaClient() as client:
            result = client.validate_dbc(dbc)

        osr = [i for i in result["issues"] if i["code"] == "offset_scale_range"]
        assert len(osr) == 1
        assert "minimum" in osr[0]["detail"]

    def test_with_offset_and_factor(self) -> None:
        # 16-bit unsigned, factor=Fraction("0.01"), offset=-100 → phys ∈ [-100, 555.35]
        """Verify with offset and factor."""
        dbc = _make_dbc(
            [
                _make_message(
                    0x100,
                    "Msg1",
                    [
                        _make_signal(
                            "Scaled",
                            start_bit=0,
                            length=16,
                            factor=Fraction("0.01"),
                            offset=-100,
                            minimum=-100,
                            maximum=Fraction("555.35"),
                        ),
                    ],
                ),
            ]
        )
        with AletheiaClient() as client:
            result = client.validate_dbc(dbc)

        osr = [i for i in result["issues"] if i["code"] == "offset_scale_range"]
        assert osr == []


class TestEmptyMessage:
    """Check 14: Message with no signals."""

    def test_empty_message_warned(self) -> None:
        """Verify empty message warned."""
        dbc = _make_dbc(
            [
                _make_message(0x100, "Empty", []),
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
        dbc = _make_dbc(
            [
                _make_message(0x100, "HasSigs", [_make_signal("Sig1")]),
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
        dbc = _make_dbc(
            [
                _make_message(
                    0x100,
                    "Msg1",
                    [
                        _make_signal("OkStart", start_bit=63, length=1, maximum=1),
                    ],
                ),
            ]
        )
        with AletheiaClient() as client:
            result = client.validate_dbc(dbc)

        sb_issues = [i for i in result["issues"] if i["code"] == "start_bit_out_of_range"]
        assert sb_issues == []

    def test_start_bit_0_ok(self) -> None:
        """Verify start bit 0 ok."""
        dbc = _make_dbc(
            [
                _make_message(
                    0x100,
                    "Msg1",
                    [
                        _make_signal("OkStart", start_bit=0, length=8),
                    ],
                ),
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
        dbc = _make_dbc(
            [
                _make_message(
                    0x100,
                    "Msg1",
                    [
                        _make_signal("Counter", start_bit=0, length=32, maximum=4294967295),
                    ],
                ),
            ]
        )
        with AletheiaClient() as client:
            result = client.validate_dbc(dbc)

        bl_issues = [i for i in result["issues"] if i["code"] == "bit_length_excessive"]
        assert bl_issues == []

    def test_bit_length_1_ok(self) -> None:
        """Verify bit length 1 ok."""
        dbc = _make_dbc(
            [
                _make_message(
                    0x100,
                    "Msg1",
                    [
                        _make_signal("OneBit", start_bit=0, length=1, maximum=1),
                    ],
                ),
            ]
        )
        with AletheiaClient() as client:
            result = client.validate_dbc(dbc)

        bl_issues = [i for i in result["issues"] if i["code"] == "bit_length_excessive"]
        assert bl_issues == []


class TestMultiValueMuxSelector:
    """Check 24: warning-class mirror of the round-trip multi-value-mux diagnostic.

    A signal multiplexed on more than one selector value loads and streams
    fine, but ``.dbc`` text cannot express it (``format_dbc_text`` refuses the
    shape with the same code), so validation names it with a warning that
    never blocks the load.
    """

    @staticmethod
    def _multi_value_dbc() -> DBCDefinition:
        return _make_dbc(
            [
                _make_message(
                    0x100,
                    "Msg1",
                    [
                        _make_signal("Mux", start_bit=0, length=8),
                        mux_signal("Payload", "Mux", [1, 2], start_bit=8, length=8),
                    ],
                ),
            ]
        )

    def test_multi_value_selector_warned(self) -> None:
        """A multi-value selector draws the warning; has_errors stays False."""
        with AletheiaClient() as client:
            result = client.validate_dbc(self._multi_value_dbc())

        assert result["has_errors"] is False
        pairs = [(i["severity"], i["code"]) for i in result["issues"]]
        assert ("warning", "multi_value_mux_selector") in pairs

    def test_singleton_selector_clean(self) -> None:
        """The singleton-selector control reports no mirror warning."""
        dbc = _make_dbc(
            [
                _make_message(
                    0x100,
                    "Msg1",
                    [
                        _make_signal("Mux", start_bit=0, length=8),
                        _make_mux_signal("Payload", "Mux", 1, start_bit=8, length=8),
                    ],
                ),
            ]
        )
        with AletheiaClient() as client:
            result = client.validate_dbc(dbc)

        codes = [i["code"] for i in result["issues"]]
        assert "multi_value_mux_selector" not in codes

    def test_load_succeeds_with_warning(self) -> None:
        """parse_dbc loads the shape and surfaces the warning without blocking."""
        with AletheiaClient() as client:
            response = client.parse_dbc(self._multi_value_dbc())

        assert response["status"] == "success", response
        codes = [w["code"] for w in response["warnings"]]
        assert "multi_value_mux_selector" in codes


class TestMuxMasterIncoherent:
    """Check 25: warning-class mirror of the round-trip master-coherence diagnostic.

    The split-master shape (slaves under two Always masters) passes every
    error-class mux check — each named master exists and there is no cycle —
    but ``.dbc`` text keeps a single ``M`` marker, so re-parsing the emitted
    text would rebind every slave to one master (``format_dbc_text`` refuses
    the shape with the same code).  Validation names it with a warning that
    never blocks the load.
    """

    @staticmethod
    def _split_master_dbc() -> DBCDefinition:
        return _make_dbc(
            [
                _make_message(
                    0x100,
                    "Msg1",
                    [
                        _make_signal("MuxA", start_bit=0, length=8),
                        _make_signal("MuxB", start_bit=8, length=8),
                        _make_mux_signal("A", "MuxA", 0, start_bit=16, length=8),
                        _make_mux_signal("B", "MuxB", 0, start_bit=24, length=8),
                    ],
                ),
            ]
        )

    def test_split_master_warned(self) -> None:
        """Slaves under two Always masters draw the warning; no errors."""
        with AletheiaClient() as client:
            result = client.validate_dbc(self._split_master_dbc())

        assert result["has_errors"] is False
        pairs = [(i["severity"], i["code"]) for i in result["issues"]]
        assert ("warning", "mux_master_incoherent") in pairs

    def test_single_master_clean(self) -> None:
        """The coherent single-master control reports no mirror warning."""
        dbc = _make_dbc(
            [
                _make_message(
                    0x100,
                    "Msg1",
                    [
                        _make_signal("Mux", start_bit=0, length=8),
                        _make_mux_signal("A", "Mux", 0, start_bit=16, length=8),
                        _make_mux_signal("B", "Mux", 1, start_bit=24, length=8),
                    ],
                ),
            ]
        )
        with AletheiaClient() as client:
            result = client.validate_dbc(dbc)

        codes = [i["code"] for i in result["issues"]]
        assert "mux_master_incoherent" not in codes

    def test_load_succeeds_with_warning(self) -> None:
        """parse_dbc loads the split-master shape and surfaces the warning."""
        with AletheiaClient() as client:
            response = client.parse_dbc(self._split_master_dbc())

        assert response["status"] == "success", response
        codes = [w["code"] for w in response["warnings"]]
        assert "mux_master_incoherent" in codes


class TestParseDBCDualLayerValidation:
    """Tests that parseDBC runs validateDBCFull as a second validation layer."""

    def test_parse_dbc_rejects_duplicate_ids(self) -> None:
        """ParseDBC should reject a DBC with duplicate message IDs."""
        dbc = _make_dbc(
            [
                _make_message(0x100, "Msg1", [_make_signal("Sig1")]),
                _make_message(0x100, "Msg2", [_make_signal("Sig2")]),
            ]
        )
        with AletheiaClient() as client:
            response = client.parse_dbc(dbc)

        assert response["status"] == "error"
        assert "validation failed" in response.get("message", "").lower()

    def test_parse_dbc_accepts_valid(self) -> None:
        """ParseDBC should accept a clean DBC."""
        dbc = _make_dbc(
            [
                _make_message(0x100, "Msg1", [_make_signal("Sig1")]),
                _make_message(0x200, "Msg2", [_make_signal("Sig2")]),
            ]
        )
        with AletheiaClient() as client:
            response = client.parse_dbc(dbc)

        assert response["status"] == "success"


# validate_dbc must reject wire responses with unknown severity strings.
#
# Agda only emits "error" or "warning". A different value means the wire
# protocol has drifted — treat it as a ProtocolError for cross-binding
# parity with C++ and Go.


def test_unknown_severity_raises_protocol_error(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    """Verify unknown severity raises protocol error."""
    dbc = _make_dbc([_make_message(0x100, "Msg1", [_make_signal("Sig1")])])
    with AletheiaClient() as client:

        def fake_send(_cmd: Command) -> Response:
            # Inject a deliberately-unknown issue severity to exercise the
            # client's validation-response rejection path.
            return cast(
                "Response",
                {
                    "status": "validation",
                    "has_errors": False,
                    "issues": [{"severity": "info", "code": "empty_message", "detail": "x"}],
                },
            )

        monkeypatch.setattr(client, "_send_command", fake_send)
        with pytest.raises(ProtocolError, match="severity"):
            client.validate_dbc(dbc)
