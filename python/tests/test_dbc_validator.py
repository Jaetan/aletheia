"""Tests for DBC validation via the Agda validator.

Tests that the Aletheia engine's validateDBC command correctly detects
structural issues in DBC definitions (duplicate IDs, duplicate signal
names, factor zero, multiplexor issues, global name collisions,
min > max).
"""

import pytest

from aletheia import AletheiaClient
from aletheia.protocols import DBCDefinition, ValidationResponse


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
        "multiplex_value": mux_value,
    }


class TestValidDBCPassesClean:
    """Tests that valid DBCs produce no issues."""

    def test_valid_single_message(self) -> None:
        dbc = _make_dbc([
            _make_message(0x100, "Msg1", [
                _make_signal("Speed", start_bit=0, length=16),
                _make_signal("RPM", start_bit=16, length=16),
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
                _make_signal("Speed", start_bit=0, length=16),
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

        assert result["has_errors"] is True
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
        assert "structural validation failed" in response.get("message", "").lower()

    def test_parse_dbc_accepts_valid(self) -> None:
        """parseDBC should accept a clean DBC."""
        dbc = _make_dbc([
            _make_message(0x100, "Msg1", [_make_signal("Sig1")]),
            _make_message(0x200, "Msg2", [_make_signal("Sig2")]),
        ])
        with AletheiaClient() as client:
            response = client.parse_dbc(dbc)

        assert response["status"] == "success"
