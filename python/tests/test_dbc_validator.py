"""Tests for DBC validation via the Agda validator.

Tests that the Aletheia engine's validateDBC command correctly detects
structural issues in DBC definitions (duplicate IDs, duplicate signal
names, factor zero, multiplexor issues, global name collisions,
min > max).
"""

import pytest

from aletheia import AletheiaClient
from aletheia.client._types import ProtocolError
from aletheia.protocols import DBCDefinition


def _make_dbc(messages: list[dict]) -> DBCDefinition:
    """Helper to build a minimal DBC with given messages."""
    return {"version": "1.0", "messages": messages}


def _make_message(
    msg_id: int,
    name: str,
    signals: list[dict] | None = None,
    *,
    dlc: int = 8,
    sender: str = "ECU",
) -> dict:
    """Helper to build a DBC message."""
    return {
        "id": msg_id,
        "name": name,
        "dlc": dlc,
        "sender": sender,
        "signals": signals or [],
    }


def _make_signal(
    name: str,
    *,
    start_bit: int = 0,
    length: int = 8,
    factor: float = 1.0,
    offset: float = 0.0,
    minimum: float = 0.0,
    maximum: float = 255.0,
    signed: bool = False,
    byte_order: str = "little_endian",
    unit: str = "",
    presence: str = "always",
) -> dict:
    """Helper to build a DBC signal."""
    sig: dict = {
        "name": name,
        "startBit": start_bit,
        "length": length,
        "byteOrder": byte_order,
        "signed": signed,
        "factor": factor,
        "offset": offset,
        "minimum": minimum,
        "maximum": maximum,
        "unit": unit,
        "presence": presence,
    }
    return sig


def _make_mux_signal(
    name: str,
    multiplexor: str,
    mux_value: int,
    *,
    start_bit: int = 0,
    length: int = 8,
) -> dict:
    """Helper to build a multiplexed DBC signal."""
    return {
        "name": name,
        "startBit": start_bit,
        "length": length,
        "byteOrder": "little_endian",
        "signed": False,
        "factor": 1.0,
        "offset": 0.0,
        "minimum": 0.0,
        "maximum": 255.0,
        "unit": "",
        "multiplexor": multiplexor,
        "multiplex_values": [mux_value],
    }


class TestValidDBCPassesClean:
    """Tests that valid DBCs produce no issues."""

    def test_valid_single_message(self) -> None:
        dbc = _make_dbc([
            _make_message(0x100, "Msg1", [
                _make_signal("Speed", start_bit=0, length=16, maximum=65535.0),
                _make_signal("RPM", start_bit=16, length=16, maximum=65535.0),
            ]),
        ])
        with AletheiaClient() as client:
            result = client.validate_dbc(dbc)

        assert result["status"] == "validation"
        assert result["has_errors"] is False
        assert result["issues"] == []

    def test_valid_multiple_messages(self) -> None:
        dbc = _make_dbc([
            _make_message(0x100, "Engine", [
                _make_signal("Speed", start_bit=0, length=16, maximum=65535.0),
            ]),
            _make_message(0x200, "Brakes", [
                _make_signal("BrakePressure", start_bit=0, length=8),
            ]),
        ])
        with AletheiaClient() as client:
            result = client.validate_dbc(dbc)

        assert result["has_errors"] is False
        assert result["issues"] == []


class TestDuplicateMessageId:
    """Check 1: Duplicate message IDs across the DBC."""

    def test_duplicate_message_id_detected(self) -> None:
        dbc = _make_dbc([
            _make_message(0x100, "Msg1", [_make_signal("Sig1")]),
            _make_message(0x100, "Msg2", [_make_signal("Sig2")]),
        ])
        with AletheiaClient() as client:
            result = client.validate_dbc(dbc)

        assert result["has_errors"] is True
        codes = [i["code"] for i in result["issues"]]
        assert "duplicate_message_id" in codes

    def test_different_ids_no_duplicate(self) -> None:
        dbc = _make_dbc([
            _make_message(0x100, "Msg1", [_make_signal("Sig1")]),
            _make_message(0x200, "Msg2", [_make_signal("Sig2")]),
        ])
        with AletheiaClient() as client:
            result = client.validate_dbc(dbc)

        dup_codes = [i for i in result["issues"] if i["code"] == "duplicate_message_id"]
        assert dup_codes == []


class TestDuplicateSignalName:
    """Check 2: Duplicate signal names within a single message."""

    def test_duplicate_signal_name_detected(self) -> None:
        dbc = _make_dbc([
            _make_message(0x100, "Msg1", [
                _make_signal("Speed", start_bit=0, length=8),
                _make_signal("Speed", start_bit=8, length=8),
            ]),
        ])
        with AletheiaClient() as client:
            result = client.validate_dbc(dbc)

        assert result["has_errors"] is True
        codes = [i["code"] for i in result["issues"]]
        assert "duplicate_signal_name" in codes


class TestFactorZero:
    """Check 3: Signal factor must not be zero."""

    def test_factor_zero_detected(self) -> None:
        dbc = _make_dbc([
            _make_message(0x100, "Msg1", [
                _make_signal("BadSignal", factor=0.0),
            ]),
        ])
        with AletheiaClient() as client:
            result = client.validate_dbc(dbc)

        assert result["has_errors"] is True
        codes = [i["code"] for i in result["issues"]]
        assert "factor_zero" in codes

    def test_nonzero_factor_ok(self) -> None:
        dbc = _make_dbc([
            _make_message(0x100, "Msg1", [
                _make_signal("GoodSignal", factor=0.01),
            ]),
        ])
        with AletheiaClient() as client:
            result = client.validate_dbc(dbc)

        factor_issues = [i for i in result["issues"] if i["code"] == "factor_zero"]
        assert factor_issues == []


class TestMinExceedsMax:
    """Check 7: Signal minimum must not exceed maximum."""

    def test_min_exceeds_max_detected(self) -> None:
        dbc = _make_dbc([
            _make_message(0x100, "Msg1", [
                _make_signal("BadRange", minimum=100.0, maximum=50.0),
            ]),
        ])
        with AletheiaClient() as client:
            result = client.validate_dbc(dbc)

        # min_exceeds_max is a warning, not an error
        assert result["has_errors"] is False
        codes = [i["code"] for i in result["issues"]]
        assert "min_exceeds_max" in codes


class TestGlobalNameCollision:
    """Check 6: Signal names must be globally unique across all messages."""

    def test_global_name_collision_detected(self) -> None:
        dbc = _make_dbc([
            _make_message(0x100, "Msg1", [
                _make_signal("SharedName", start_bit=0, length=8),
            ]),
            _make_message(0x200, "Msg2", [
                _make_signal("SharedName", start_bit=0, length=8),
            ]),
        ])
        with AletheiaClient() as client:
            result = client.validate_dbc(dbc)

        codes = [i["code"] for i in result["issues"]]
        assert "global_name_collision" in codes


class TestSignalExceedsDLC:
    """Check 8: Signal bit range must fit within DLC × 8 bits."""

    def test_little_endian_signal_exceeds_dlc(self) -> None:
        dbc = _make_dbc([
            _make_message(0x100, "Msg1", [
                _make_signal("TooWide", start_bit=56, length=16, byte_order="little_endian"),
            ], dlc=8),
        ])
        with AletheiaClient() as client:
            result = client.validate_dbc(dbc)

        codes = [i["code"] for i in result["issues"]]
        assert "signal_exceeds_dlc" in codes

    def test_little_endian_signal_fits_dlc(self) -> None:
        dbc = _make_dbc([
            _make_message(0x100, "Msg1", [
                _make_signal("Fits", start_bit=0, length=16, byte_order="little_endian"),
            ], dlc=8),
        ])
        with AletheiaClient() as client:
            result = client.validate_dbc(dbc)

        exceeds = [i for i in result["issues"] if i["code"] == "signal_exceeds_dlc"]
        assert exceeds == []

    def test_big_endian_signal_exceeds_dlc(self) -> None:
        # BE signals that overflow the frame are now rejected by the JSON
        # parser's `physicalGate` (PhysicallyValid enforcement) before the
        # validator runs — system review §12.1, parser produces
        # WellFormedDBCRT directly. This test documents the new layer:
        # parse_signal_overflows_frame surfaces here instead of the
        # downstream validator's signal_exceeds_dlc.
        dbc = _make_dbc([
            _make_message(0x100, "Msg1", [
                _make_signal("TooWide", start_bit=7, length=33, byte_order="big_endian",
                             maximum=255.0),
            ], dlc=4),
        ])
        with AletheiaClient() as client:
            with pytest.raises(ProtocolError, match="overflows frame"):
                client.validate_dbc(dbc)

    def test_big_endian_signal_fits_dlc(self) -> None:
        # BitsInFrame checks startBit + bitLength ≤ dlc * 8 on the
        # CONVERTED start bit. convertStartBit uses actual DLC.
        # startBit=7, length=8, dlc=4 → physBit=31, converted=24,
        # 24+8=32 ≤ 4*8=32 → fits
        dbc = _make_dbc([
            _make_message(0x100, "Msg1", [
                _make_signal("Fits", start_bit=7, length=8, byte_order="big_endian",
                             maximum=255.0),
            ], dlc=4),
        ])
        with AletheiaClient() as client:
            result = client.validate_dbc(dbc)

        exceeds = [i for i in result["issues"] if i["code"] == "signal_exceeds_dlc"]
        assert exceeds == []

    def test_small_dlc_catches_overflow(self) -> None:
        # DLC=2 means only 16 bits; signal at bit 16 with length 8 exceeds
        dbc = _make_dbc([
            _make_message(0x100, "Msg1", [
                _make_signal("Overflow", start_bit=16, length=8, byte_order="little_endian"),
            ], dlc=2),
        ])
        with AletheiaClient() as client:
            result = client.validate_dbc(dbc)

        codes = [i["code"] for i in result["issues"]]
        assert "signal_exceeds_dlc" in codes


class TestSignalOverlap:
    """Check 9: Non-multiplexed coexisting signals must not share bits."""

    def test_overlapping_signals_detected(self) -> None:
        dbc = _make_dbc([
            _make_message(0x100, "Msg1", [
                _make_signal("Sig1", start_bit=0, length=16),
                _make_signal("Sig2", start_bit=8, length=16),
            ]),
        ])
        with AletheiaClient() as client:
            result = client.validate_dbc(dbc)

        codes = [i["code"] for i in result["issues"]]
        assert "signal_overlap" in codes

    def test_non_overlapping_signals_ok(self) -> None:
        dbc = _make_dbc([
            _make_message(0x100, "Msg1", [
                _make_signal("Sig1", start_bit=0, length=8),
                _make_signal("Sig2", start_bit=8, length=8),
            ]),
        ])
        with AletheiaClient() as client:
            result = client.validate_dbc(dbc)

        overlaps = [i for i in result["issues"] if i["code"] == "signal_overlap"]
        assert overlaps == []

    def test_multiplexed_signals_can_share_bits(self) -> None:
        """Multiplexed signals that can't coexist should not report overlap."""
        dbc = _make_dbc([
            _make_message(0x100, "Msg1", [
                _make_signal("Mux", start_bit=0, length=8),
                _make_mux_signal("A", "Mux", 0, start_bit=8, length=8),
                _make_mux_signal("B", "Mux", 1, start_bit=8, length=8),
            ]),
        ])
        with AletheiaClient() as client:
            result = client.validate_dbc(dbc)

        overlaps = [i for i in result["issues"] if i["code"] == "signal_overlap"]
        assert overlaps == []


class TestBitLengthZero:
    """Check 10: Signal bit length must not be zero."""

    def test_zero_length_detected(self) -> None:
        dbc = _make_dbc([
            _make_message(0x100, "Msg1", [
                _make_signal("ZeroLen", length=0),
            ]),
        ])
        with AletheiaClient() as client:
            result = client.validate_dbc(dbc)

        codes = [i["code"] for i in result["issues"]]
        assert "bit_length_zero" in codes

    def test_nonzero_length_ok(self) -> None:
        dbc = _make_dbc([
            _make_message(0x100, "Msg1", [
                _make_signal("Normal", length=8),
            ]),
        ])
        with AletheiaClient() as client:
            result = client.validate_dbc(dbc)

        zero_issues = [i for i in result["issues"] if i["code"] == "bit_length_zero"]
        assert zero_issues == []


class TestDuplicateMessageName:
    """Check 11: Duplicate message names across the DBC."""

    def test_duplicate_name_detected(self) -> None:
        dbc = _make_dbc([
            _make_message(0x100, "SameName", [_make_signal("Sig1")]),
            _make_message(0x200, "SameName", [_make_signal("Sig2")]),
        ])
        with AletheiaClient() as client:
            result = client.validate_dbc(dbc)

        codes = [i["code"] for i in result["issues"]]
        assert "duplicate_message_name" in codes

    def test_different_names_ok(self) -> None:
        dbc = _make_dbc([
            _make_message(0x100, "Msg1", [_make_signal("Sig1")]),
            _make_message(0x200, "Msg2", [_make_signal("Sig2")]),
        ])
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
        dbc = _make_dbc([
            _make_message(0x100, "Msg1", [
                _make_signal("Good", length=8, factor=1.0, offset=0.0,
                             minimum=0.0, maximum=255.0),
            ]),
        ])
        with AletheiaClient() as client:
            result = client.validate_dbc(dbc)

        osr = [i for i in result["issues"] if i["code"] == "offset_scale_range"]
        assert osr == []

    def test_unsigned_declared_max_too_narrow(self) -> None:
        # 8-bit unsigned, factor=1, offset=0 → phys_max=255, but declared max=200
        dbc = _make_dbc([
            _make_message(0x100, "Msg1", [
                _make_signal("Narrow", length=8, factor=1.0, offset=0.0,
                             minimum=0.0, maximum=200.0),
            ]),
        ])
        with AletheiaClient() as client:
            result = client.validate_dbc(dbc)

        osr = [i for i in result["issues"] if i["code"] == "offset_scale_range"]
        assert len(osr) == 1
        assert "maximum" in osr[0]["detail"]

    def test_signed_correct_range_clean(self) -> None:
        # 8-bit signed, factor=1, offset=0 → phys ∈ [-128, 127]
        dbc = _make_dbc([
            _make_message(0x100, "Msg1", [
                _make_signal("Temp", length=8, signed=True, factor=1.0,
                             offset=0.0, minimum=-128.0, maximum=127.0),
            ]),
        ])
        with AletheiaClient() as client:
            result = client.validate_dbc(dbc)

        osr = [i for i in result["issues"] if i["code"] == "offset_scale_range"]
        assert osr == []

    def test_signed_declared_min_too_narrow(self) -> None:
        # 8-bit signed, factor=1, offset=0 → phys_min=-128, but declared min=-100
        # Declared range [-100, 127] is NARROWER than physical [-128, 127]
        # Hardware can produce values in [-128, -101] outside declared range → warning
        dbc = _make_dbc([
            _make_message(0x100, "Msg1", [
                _make_signal("Cold", length=8, signed=True, factor=1.0,
                             offset=0.0, minimum=-100.0, maximum=127.0),
            ]),
        ])
        with AletheiaClient() as client:
            result = client.validate_dbc(dbc)

        osr = [i for i in result["issues"] if i["code"] == "offset_scale_range"]
        assert len(osr) == 1
        assert "minimum" in osr[0]["detail"]

    def test_negative_factor_unsigned(self) -> None:
        # 8-bit unsigned, factor=-0.1, offset=25.5
        # phys_min = 255 * (-0.1) + 25.5 = 0.0, phys_max = 0 * (-0.1) + 25.5 = 25.5
        dbc = _make_dbc([
            _make_message(0x100, "Msg1", [
                _make_signal("Inverted", length=8, factor=-0.1, offset=25.5,
                             minimum=0.0, maximum=25.5),
            ]),
        ])
        with AletheiaClient() as client:
            result = client.validate_dbc(dbc)

        osr = [i for i in result["issues"] if i["code"] == "offset_scale_range"]
        assert osr == []

    def test_negative_factor_wrong_range_warns(self) -> None:
        # 8-bit unsigned, factor=-0.1, offset=25.5
        # phys range: [0.0, 25.5] (factor negative flips raw→phys direction)
        # Declared min=5.0 is ABOVE physMin=0.0 → hardware can produce [0, 5) outside declared range
        dbc = _make_dbc([
            _make_message(0x100, "Msg1", [
                _make_signal("Bad", length=8, factor=-0.1, offset=25.5,
                             minimum=5.0, maximum=25.5),
            ]),
        ])
        with AletheiaClient() as client:
            result = client.validate_dbc(dbc)

        osr = [i for i in result["issues"] if i["code"] == "offset_scale_range"]
        assert len(osr) == 1
        assert "minimum" in osr[0]["detail"]

    def test_with_offset_and_factor(self) -> None:
        # 16-bit unsigned, factor=0.01, offset=-100 → phys ∈ [-100, 555.35]
        dbc = _make_dbc([
            _make_message(0x100, "Msg1", [
                _make_signal("Scaled", start_bit=0, length=16, factor=0.01,
                             offset=-100.0, minimum=-100.0, maximum=555.35),
            ]),
        ])
        with AletheiaClient() as client:
            result = client.validate_dbc(dbc)

        osr = [i for i in result["issues"] if i["code"] == "offset_scale_range"]
        assert osr == []


class TestEmptyMessage:
    """Check 14: Message with no signals."""

    def test_empty_message_warned(self) -> None:
        dbc = _make_dbc([
            _make_message(0x100, "Empty", []),
        ])
        with AletheiaClient() as client:
            result = client.validate_dbc(dbc)

        codes = [i["code"] for i in result["issues"]]
        assert "empty_message" in codes
        # Should be warning, not error
        empty_issues = [i for i in result["issues"] if i["code"] == "empty_message"]
        assert all(i["severity"] == "warning" for i in empty_issues)

    def test_message_with_signals_ok(self) -> None:
        dbc = _make_dbc([
            _make_message(0x100, "HasSigs", [_make_signal("Sig1")]),
        ])
        with AletheiaClient() as client:
            result = client.validate_dbc(dbc)

        empty_issues = [i for i in result["issues"] if i["code"] == "empty_message"]
        assert empty_issues == []


class TestStartBitOutOfRange:
    """Check 15: Start bit >= 64 is suspicious.

    Note: DBC parser clamps startBit via % 64, so values >= 64 wrap to 0.
    This check is defense-in-depth for programmatically constructed DBCs.
    We test with values within the parser's range (0-63).
    """

    def test_start_bit_63_ok(self) -> None:
        dbc = _make_dbc([
            _make_message(0x100, "Msg1", [
                _make_signal("OkStart", start_bit=63, length=1, maximum=1.0),
            ]),
        ])
        with AletheiaClient() as client:
            result = client.validate_dbc(dbc)

        sb_issues = [i for i in result["issues"] if i["code"] == "start_bit_out_of_range"]
        assert sb_issues == []

    def test_start_bit_0_ok(self) -> None:
        dbc = _make_dbc([
            _make_message(0x100, "Msg1", [
                _make_signal("OkStart", start_bit=0, length=8),
            ]),
        ])
        with AletheiaClient() as client:
            result = client.validate_dbc(dbc)

        sb_issues = [i for i in result["issues"] if i["code"] == "start_bit_out_of_range"]
        assert sb_issues == []


class TestBitLengthExcessive:
    """Check 16: Bit length > 64 is suspicious.

    Note: DBC parser clamps bitLength via % 65, so values >= 65 wrap.
    This check is defense-in-depth for programmatically constructed DBCs.
    We test with values within the parser's range (0-64).
    """

    def test_bit_length_32_ok(self) -> None:
        # Test with 32-bit signal — well within the 64-bit limit
        dbc = _make_dbc([
            _make_message(0x100, "Msg1", [
                _make_signal("Counter", start_bit=0, length=32,
                             maximum=4294967295.0),
            ]),
        ])
        with AletheiaClient() as client:
            result = client.validate_dbc(dbc)

        bl_issues = [i for i in result["issues"] if i["code"] == "bit_length_excessive"]
        assert bl_issues == []

    def test_bit_length_1_ok(self) -> None:
        dbc = _make_dbc([
            _make_message(0x100, "Msg1", [
                _make_signal("OneBit", start_bit=0, length=1, maximum=1.0),
            ]),
        ])
        with AletheiaClient() as client:
            result = client.validate_dbc(dbc)

        bl_issues = [i for i in result["issues"] if i["code"] == "bit_length_excessive"]
        assert bl_issues == []


class TestParseDBC_DualLayerValidation:
    """Tests that parseDBC runs validateDBCFull as a second validation layer."""

    def test_parse_dbc_rejects_duplicate_ids(self) -> None:
        """parseDBC should reject a DBC with duplicate message IDs."""
        dbc = _make_dbc([
            _make_message(0x100, "Msg1", [_make_signal("Sig1")]),
            _make_message(0x100, "Msg2", [_make_signal("Sig2")]),
        ])
        with AletheiaClient() as client:
            response = client.parse_dbc(dbc)

        assert response["status"] == "error"
        assert "validation failed" in response.get("message", "").lower()

    def test_parse_dbc_accepts_valid(self) -> None:
        """parseDBC should accept a clean DBC."""
        dbc = _make_dbc([
            _make_message(0x100, "Msg1", [_make_signal("Sig1")]),
            _make_message(0x200, "Msg2", [_make_signal("Sig2")]),
        ])
        with AletheiaClient() as client:
            response = client.parse_dbc(dbc)

        assert response["status"] == "success"


class TestValidateDBC_UnknownSeverityRejected:
    """validate_dbc must reject wire responses with unknown severity strings.

    Agda only emits "error" or "warning". A different value means the wire
    protocol has drifted — treat it as a ProtocolError for cross-binding
    parity with C++ and Go.
    """

    def test_unknown_severity_raises_protocol_error(
        self, monkeypatch: pytest.MonkeyPatch
    ) -> None:
        dbc = _make_dbc([_make_message(0x100, "Msg1", [_make_signal("Sig1")])])
        with AletheiaClient() as client:
            def fake_send(_cmd: object) -> dict:
                return {
                    "status": "validation",
                    "has_errors": False,
                    "issues": [
                        {"severity": "info", "code": "empty_message", "detail": "x"}
                    ],
                }

            monkeypatch.setattr(client, "_send_command", fake_send)
            with pytest.raises(ProtocolError, match="severity"):
                client.validate_dbc(dbc)
