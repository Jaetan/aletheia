# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
"""Tests for DBC validation via the Agda validator.

Tests that the Aletheia engine's validateDBC command correctly detects
structural issues in DBC definitions (duplicate IDs and names, global name
collisions, factor zero, min > max, offset and scale range, multiplexor
issues) and refuses a malformed validation response.  The checks on where a
signal sits in its message's frame are in ``test_dbc_validator_layout.py``.
"""

from fractions import Fraction
from typing import TYPE_CHECKING, cast

import pytest
from _dbc_helpers import mux_signal
from _validator_helpers import (
    make_dbc,
    make_message,
    make_mux_signal,
    make_signal,
    single_message_dbc,
)

from aletheia import AletheiaClient, DBCDefinition, ProtocolError

if TYPE_CHECKING:
    from aletheia.types import (
        Command,
        Response,
    )


class TestValidDBCPassesClean:
    """Tests that valid DBCs produce no issues."""

    def test_valid_single_message(self) -> None:
        """Verify valid single message."""
        dbc = single_message_dbc(
            [
                make_signal("Speed", start_bit=0, length=16, maximum=65535),
                make_signal("RPM", start_bit=16, length=16, maximum=65535),
            ]
        )
        with AletheiaClient() as client:
            result = client.validate_dbc(dbc)

        assert result["status"] == "validation"
        assert result["has_errors"] is False
        assert result["issues"] == []

    def test_valid_multiple_messages(self) -> None:
        """Verify valid multiple messages."""
        dbc = make_dbc(
            [
                make_message(
                    0x100,
                    "Engine",
                    [
                        make_signal("Speed", start_bit=0, length=16, maximum=65535),
                    ],
                ),
                make_message(
                    0x200,
                    "Brakes",
                    [
                        make_signal("BrakePressure", start_bit=0, length=8),
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
        dbc = make_dbc(
            [
                make_message(0x100, "Msg1", [make_signal("Sig1")]),
                make_message(0x100, "Msg2", [make_signal("Sig2")]),
            ]
        )
        with AletheiaClient() as client:
            result = client.validate_dbc(dbc)

        assert result["has_errors"] is True
        codes = [i["code"] for i in result["issues"]]
        assert "duplicate_message_id" in codes

    def test_different_ids_no_duplicate(self) -> None:
        """Verify different ids no duplicate."""
        dbc = make_dbc(
            [
                make_message(0x100, "Msg1", [make_signal("Sig1")]),
                make_message(0x200, "Msg2", [make_signal("Sig2")]),
            ]
        )
        with AletheiaClient() as client:
            result = client.validate_dbc(dbc)

        dup_codes = [i for i in result["issues"] if i["code"] == "duplicate_message_id"]
        assert dup_codes == []


# Check 2: Duplicate signal names within a single message.


def test_duplicate_signal_name_detected() -> None:
    """Verify duplicate signal name detected."""
    dbc = single_message_dbc(
        [
            make_signal("Speed", start_bit=0, length=8),
            make_signal("Speed", start_bit=8, length=8),
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
        dbc = single_message_dbc(
            [
                make_signal("BadSignal", factor=0),
            ]
        )
        with AletheiaClient() as client:
            result = client.validate_dbc(dbc)

        assert result["has_errors"] is True
        codes = [i["code"] for i in result["issues"]]
        assert "factor_zero" in codes

    def test_nonzero_factor_ok(self) -> None:
        """Verify nonzero factor ok."""
        dbc = single_message_dbc(
            [
                make_signal("GoodSignal", factor=Fraction("0.01")),
            ]
        )
        with AletheiaClient() as client:
            result = client.validate_dbc(dbc)

        factor_issues = [i for i in result["issues"] if i["code"] == "factor_zero"]
        assert factor_issues == []


# Check 7: Signal minimum must not exceed maximum.


def test_min_exceeds_max_detected() -> None:
    """Verify min exceeds max detected."""
    dbc = single_message_dbc(
        [
            make_signal("BadRange", minimum=100, maximum=50),
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
    dbc = make_dbc(
        [
            make_message(
                0x100,
                "Msg1",
                [
                    make_signal("SharedName", start_bit=0, length=8),
                ],
            ),
            make_message(
                0x200,
                "Msg2",
                [
                    make_signal("SharedName", start_bit=0, length=8),
                ],
            ),
        ]
    )
    with AletheiaClient() as client:
        result = client.validate_dbc(dbc)

    codes = [i["code"] for i in result["issues"]]
    assert "global_name_collision" in codes


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
        sig = make_mux_signal("Mode", "Mux", 0, start_bit=0, length=8)
        # Adversarial: a float is not a valid JSON natural; the parser must reject.
        sig["multiplex_values"] = cast("list[int]", [1.5])
        dbc = single_message_dbc([sig])
        with AletheiaClient() as client, pytest.raises(ProtocolError) as excinfo:
            client.validate_dbc(dbc)
        assert excinfo.value.code == "parse_non_integer_multiplex_value"

    def test_string_in_multiplex_values_rejected(self) -> None:
        """Non-numeric in multiplex_values also surfaces the same typed code."""
        sig = make_mux_signal("Mode", "Mux", 0, start_bit=0, length=8)
        # Adversarial: a non-numeric element is not a valid JSON natural.
        sig["multiplex_values"] = cast("list[int]", ["not_a_number"])
        dbc = single_message_dbc([sig])
        with AletheiaClient() as client, pytest.raises(ProtocolError) as excinfo:
            client.validate_dbc(dbc)
        assert excinfo.value.code == "parse_non_integer_multiplex_value"


class TestDuplicateMessageName:
    """Check 11: Duplicate message names across the DBC."""

    def test_duplicate_name_detected(self) -> None:
        """Verify duplicate name detected."""
        dbc = make_dbc(
            [
                make_message(0x100, "SameName", [make_signal("Sig1")]),
                make_message(0x200, "SameName", [make_signal("Sig2")]),
            ]
        )
        with AletheiaClient() as client:
            result = client.validate_dbc(dbc)

        codes = [i["code"] for i in result["issues"]]
        assert "duplicate_message_name" in codes

    def test_different_names_ok(self) -> None:
        """Verify different names ok."""
        dbc = make_dbc(
            [
                make_message(0x100, "Msg1", [make_signal("Sig1")]),
                make_message(0x200, "Msg2", [make_signal("Sig2")]),
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
        dbc = single_message_dbc(
            [
                make_signal("Good", length=8, factor=1, offset=0, minimum=0, maximum=255),
            ]
        )
        with AletheiaClient() as client:
            result = client.validate_dbc(dbc)

        osr = [i for i in result["issues"] if i["code"] == "offset_scale_range"]
        assert osr == []

    def test_unsigned_declared_max_too_narrow(self) -> None:
        # 8-bit unsigned, factor=1, offset=0 → phys_max=255, but declared max=200
        """Verify unsigned declared max too narrow."""
        dbc = single_message_dbc(
            [
                make_signal("Narrow", length=8, factor=1, offset=0, minimum=0, maximum=200),
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
        dbc = single_message_dbc(
            [
                make_signal(
                    "Temp",
                    length=8,
                    signed=True,
                    factor=1,
                    offset=0,
                    minimum=-128,
                    maximum=127,
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
        dbc = single_message_dbc(
            [
                make_signal(
                    "Cold",
                    length=8,
                    signed=True,
                    factor=1,
                    offset=0,
                    minimum=-100,
                    maximum=127,
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
        dbc = single_message_dbc(
            [
                make_signal(
                    "Inverted",
                    length=8,
                    factor=Fraction("-0.1"),
                    offset=Fraction("25.5"),
                    minimum=0,
                    maximum=Fraction("25.5"),
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
        dbc = single_message_dbc(
            [
                make_signal(
                    "Bad",
                    length=8,
                    factor=Fraction("-0.1"),
                    offset=Fraction("25.5"),
                    minimum=5,
                    maximum=Fraction("25.5"),
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
        dbc = single_message_dbc(
            [
                make_signal(
                    "Scaled",
                    start_bit=0,
                    length=16,
                    factor=Fraction("0.01"),
                    offset=-100,
                    minimum=-100,
                    maximum=Fraction("555.35"),
                ),
            ]
        )
        with AletheiaClient() as client:
            result = client.validate_dbc(dbc)

        osr = [i for i in result["issues"] if i["code"] == "offset_scale_range"]
        assert osr == []


class TestMultiValueMuxSelector:
    """Check 24: warning-class mirror of the round-trip multi-value-mux diagnostic.

    A signal multiplexed on more than one selector value loads and streams
    fine, but ``.dbc`` text cannot express it (``format_dbc_text`` refuses the
    shape with the same code), so validation names it with a warning that
    never blocks the load.
    """

    @staticmethod
    def _multi_value_dbc() -> DBCDefinition:
        return single_message_dbc(
            [
                make_signal("Mux", start_bit=0, length=8),
                mux_signal("Payload", "Mux", [1, 2], start_bit=8, length=8),
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
        dbc = single_message_dbc(
            [
                make_signal("Mux", start_bit=0, length=8),
                make_mux_signal("Payload", "Mux", 1, start_bit=8, length=8),
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
        return single_message_dbc(
            [
                make_signal("MuxA", start_bit=0, length=8),
                make_signal("MuxB", start_bit=8, length=8),
                make_mux_signal("A", "MuxA", 0, start_bit=16, length=8),
                make_mux_signal("B", "MuxB", 0, start_bit=24, length=8),
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
        dbc = single_message_dbc(
            [
                make_signal("Mux", start_bit=0, length=8),
                make_mux_signal("A", "Mux", 0, start_bit=16, length=8),
                make_mux_signal("B", "Mux", 1, start_bit=24, length=8),
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
        dbc = make_dbc(
            [
                make_message(0x100, "Msg1", [make_signal("Sig1")]),
                make_message(0x100, "Msg2", [make_signal("Sig2")]),
            ]
        )
        with AletheiaClient() as client:
            response = client.parse_dbc(dbc)

        assert response["status"] == "error"
        assert "validation failed" in response.get("message", "").lower()

    def test_parse_dbc_accepts_valid(self) -> None:
        """ParseDBC should accept a clean DBC."""
        dbc = make_dbc(
            [
                make_message(0x100, "Msg1", [make_signal("Sig1")]),
                make_message(0x200, "Msg2", [make_signal("Sig2")]),
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
    dbc = single_message_dbc([make_signal("Sig1")])
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
