"""Tests for DBC pretty-printer (format_dbc + dbc_to_text)."""

from pathlib import Path

import pytest

from aletheia import AletheiaClient, ProtocolError, dbc_to_text
from aletheia.dbc_converter import dbc_to_json
from aletheia.protocols import DBCDefinition


EXAMPLE_DBC = Path(__file__).parent.parent.parent / "examples" / "example.dbc"


# ============================================================================
# dbc_to_text (pure Python, no FFI needed)
# ============================================================================

class TestDBCToText:
    """Tests for the Python dbc_to_text formatter."""

    def test_basic_output(self, sample_dbc: DBCDefinition) -> None:
        """dbc_to_text produces expected DBC structure."""
        text = dbc_to_text(sample_dbc)
        assert 'VERSION "1.0"' in text
        assert "BU_: TestECU" in text
        assert "BO_ 256 TestMessage: 8 TestECU" in text
        assert "SG_ TestSignal" in text

    def test_byte_order_encoding(self) -> None:
        """ByteOrder maps to correct DBC encoding (1=LE, 0=BE)."""
        dbc: DBCDefinition = {
            "version": "",
            "messages": [{
                "id": 1,
                "name": "Msg",
                "dlc": 8,
                "sender": "ECU",
                "signals": [
                    {
                        "name": "SigLE",
                        "startBit": 0,
                        "length": 8,
                        "byteOrder": "little_endian",
                        "signed": False,
                        "factor": 1.0,
                        "offset": 0.0,
                        "minimum": 0.0,
                        "maximum": 255.0,
                        "unit": "V",
                        "presence": "always",
                    },
                    {
                        "name": "SigBE",
                        "startBit": 8,
                        "length": 8,
                        "byteOrder": "big_endian",
                        "signed": True,
                        "factor": 0.5,
                        "offset": -10.0,
                        "minimum": -10.0,
                        "maximum": 117.5,
                        "unit": "A",
                        "presence": "always",
                    },
                ],
            }],
        }
        text = dbc_to_text(dbc)
        # little_endian -> @1, unsigned -> +
        assert "SigLE : 0|8@1+" in text
        # big_endian -> @0, signed -> -
        assert "SigBE : 8|8@0-" in text
        # Check factor/offset
        assert "(0.5,-10)" in text
        # Check unit
        assert '"V"' in text
        assert '"A"' in text

    def test_multiplexed_signals(self) -> None:
        """Multiplexed signals get m<value> indicator."""
        dbc: DBCDefinition = {
            "version": "",
            "messages": [{
                "id": 1,
                "name": "Msg",
                "dlc": 8,
                "sender": "ECU",
                "signals": [
                    {
                        "name": "MuxSig",
                        "startBit": 0,
                        "length": 8,
                        "byteOrder": "little_endian",
                        "signed": False,
                        "factor": 1.0,
                        "offset": 0.0,
                        "minimum": 0.0,
                        "maximum": 255.0,
                        "unit": "",
                        "multiplexor": "Selector",
                        "multiplex_value": 3,
                    },
                ],
            }],
        }
        text = dbc_to_text(dbc)
        assert "SG_ MuxSig m3 :" in text

    def test_unique_senders(self) -> None:
        """BU_ line lists each sender only once."""
        dbc: DBCDefinition = {
            "version": "",
            "messages": [
                {"id": 1, "name": "M1", "dlc": 8, "sender": "ECU_A", "signals": []},
                {"id": 2, "name": "M2", "dlc": 8, "sender": "ECU_B", "signals": []},
                {"id": 3, "name": "M3", "dlc": 8, "sender": "ECU_A", "signals": []},
            ],
        }
        text = dbc_to_text(dbc)
        assert "BU_: ECU_A ECU_B" in text

    def test_non_integer_factor(self) -> None:
        """Roundtrip a DBC with non-integer factor through Agda and dbc_to_text."""
        dbc: DBCDefinition = {
            "version": "",
            "messages": [{
                "id": 1,
                "name": "Msg",
                "dlc": 8,
                "sender": "ECU",
                "signals": [{
                    "name": "Sig",
                    "startBit": 0,
                    "length": 16,
                    "byteOrder": "little_endian",
                    "signed": False,
                    "factor": 0.25,
                    "offset": -1.5,
                    "minimum": 0.0,
                    "maximum": 100.0,
                    "unit": "rpm",
                    "presence": "always",
                }],
            }],
        }
        with AletheiaClient() as client:
            client.parse_dbc(dbc)
            formatted = client.format_dbc()
            # Agda returns rationals; format_dbc normalizes to float
            sig = formatted["messages"][0]["signals"][0]
            assert isinstance(sig["factor"], float)
            assert sig["factor"] == pytest.approx(0.25)
            assert isinstance(sig["offset"], float)
            assert sig["offset"] == pytest.approx(-1.5)
            # dbc_to_text works on the normalized output
            text = dbc_to_text(formatted)
            assert "(0.25,-1.5)" in text
            assert "[0|100]" in text

    def test_extended_frame_bit(self) -> None:
        """Extended frames get bit 31 set in BO_ line."""
        dbc: DBCDefinition = {
            "version": "",
            "messages": [{
                "id": 0x100,
                "name": "ExtMsg",
                "dlc": 8,
                "sender": "ECU",
                "extended": True,
                "signals": [],
            }],
        }
        text = dbc_to_text(dbc)
        expected_id = 0x100 | 0x80000000  # CAN Extended Frame Format flag
        assert f"BO_ {expected_id} ExtMsg:" in text

    def test_multiplexor_m_indicator(self) -> None:
        """Multiplexor signal gets M indicator when referenced by multiplexed signals."""
        dbc: DBCDefinition = {
            "version": "",
            "messages": [{
                "id": 1,
                "name": "Msg",
                "dlc": 8,
                "sender": "ECU",
                "signals": [
                    {
                        "name": "Selector",
                        "startBit": 0,
                        "length": 8,
                        "byteOrder": "little_endian",
                        "signed": False,
                        "factor": 1,
                        "offset": 0,
                        "minimum": 0,
                        "maximum": 255,
                        "unit": "",
                        "presence": "always",
                    },
                    {
                        "name": "Muxed",
                        "startBit": 8,
                        "length": 8,
                        "byteOrder": "little_endian",
                        "signed": False,
                        "factor": 1,
                        "offset": 0,
                        "minimum": 0,
                        "maximum": 255,
                        "unit": "",
                        "multiplexor": "Selector",
                        "multiplex_value": 0,
                    },
                ],
            }],
        }
        text = dbc_to_text(dbc)
        assert "SG_ Selector M :" in text
        assert "SG_ Muxed m0 :" in text

    def test_empty_messages(self) -> None:
        """DBC with no messages produces valid output."""
        dbc: DBCDefinition = {"version": "2.0", "messages": []}
        text = dbc_to_text(dbc)
        assert 'VERSION "2.0"' in text
        assert "BU_: " in text

    def test_example_dbc_roundtrip_text(self) -> None:
        """dbc_to_json -> dbc_to_text produces valid DBC text."""
        if not EXAMPLE_DBC.exists():
            pytest.skip("example.dbc not found")
        dbc_json = dbc_to_json(EXAMPLE_DBC)
        text = dbc_to_text(dbc_json)
        assert "BO_ 256 EngineStatus:" in text
        assert "SG_ EngineSpeed" in text
        assert "SG_ EngineTemp" in text
        assert "BO_ 512 BrakeStatus:" in text
        assert "SG_ BrakePressure" in text
        assert "SG_ BrakePressed" in text


# ============================================================================
# format_dbc (FFI roundtrip through Agda)
# ============================================================================

class TestFormatDBC:
    """Tests for the Agda-side formatDBC via AletheiaClient."""

    def test_no_dbc_loaded(self) -> None:
        """format_dbc raises ProtocolError when no DBC is loaded."""
        with AletheiaClient() as client:
            with pytest.raises(ProtocolError, match="DBC not loaded"):
                client.format_dbc()

    def test_roundtrip_json(self, sample_dbc: DBCDefinition) -> None:
        """parse_dbc -> format_dbc returns equivalent JSON structure."""
        with AletheiaClient() as client:
            result = client.parse_dbc(sample_dbc)
            assert result["status"] == "success"

            formatted = client.format_dbc()

            # Check top-level structure
            assert formatted["version"] == sample_dbc["version"]
            assert len(formatted["messages"]) == len(sample_dbc["messages"])

            # Check message fields
            orig_msg = sample_dbc["messages"][0]
            fmt_msg = formatted["messages"][0]
            assert fmt_msg["name"] == orig_msg["name"]
            assert fmt_msg["id"] == orig_msg["id"]
            assert fmt_msg["dlc"] == orig_msg["dlc"]
            assert fmt_msg["sender"] == orig_msg["sender"]

            # Check signal fields
            orig_sig = orig_msg["signals"][0]
            fmt_sig = fmt_msg["signals"][0]
            assert fmt_sig["name"] == orig_sig["name"]
            assert fmt_sig["startBit"] == orig_sig["startBit"]
            assert fmt_sig["length"] == orig_sig["length"]
            assert fmt_sig["byteOrder"] == orig_sig["byteOrder"]
            assert fmt_sig["signed"] == orig_sig["signed"]
            assert fmt_sig["unit"] == orig_sig["unit"]

    def test_roundtrip_example_dbc(self) -> None:
        """Roundtrip example.dbc through Agda and verify key fields match."""
        if not EXAMPLE_DBC.exists():
            pytest.skip("example.dbc not found")

        dbc_json = dbc_to_json(EXAMPLE_DBC)

        with AletheiaClient() as client:
            result = client.parse_dbc(dbc_json)
            assert result["status"] == "success"

            formatted = client.format_dbc()

            # Same number of messages
            assert len(formatted["messages"]) == len(dbc_json["messages"])

            # Check each message name and signal count
            for orig, fmt in zip(dbc_json["messages"], formatted["messages"]):
                assert fmt["name"] == orig["name"]
                assert len(fmt["signals"]) == len(orig["signals"])

    def test_format_then_text(self, sample_dbc: DBCDefinition) -> None:
        """format_dbc -> dbc_to_text produces valid DBC text."""
        with AletheiaClient() as client:
            client.parse_dbc(sample_dbc)
            formatted = client.format_dbc()
            text = dbc_to_text(formatted)

            assert "BO_ 256 TestMessage:" in text
            assert "SG_ TestSignal" in text
