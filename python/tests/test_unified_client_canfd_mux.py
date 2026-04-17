"""CAN-FD and nested-multiplexing tests for AletheiaClient.

Split out of ``test_unified_client.py`` to keep that file under the
1000-line pylint cap.  Covers two extended-frame areas:

* ``TestCANFDFrames`` — DLC codes 9–15, payloads 12–64 bytes, build/extract
  round-trips, the all-DLC sweep, and CAN-FD LTL streaming.
* ``TestNestedMultiplexing`` — multi-level multiplexor chains and the cycle
  detector.

Fixtures (``simple_dbc``) come from ``conftest.py``.
"""

import pytest

from aletheia import AletheiaClient, Signal, dlc_to_bytes
from aletheia.client._types import ProcessError


class TestCANFDFrames:
    """CAN-FD frame tests: DLC 9-15, payloads 12-64 bytes."""

    CANFD_DBC_12 = {
        "version": "1.0",
        "messages": [{
            "id": 0x200,
            "name": "CANFDMessage12",
            "dlc": 12,
            "sender": "ECU",
            "signals": [
                {
                    "name": "BaseSignal",
                    "startBit": 0,
                    "length": 8,
                    "byteOrder": "little_endian",
                    "signed": False,
                    "factor": 1.0, "offset": 0.0,
                    "minimum": 0.0, "maximum": 255.0,
                    "unit": "", "presence": "always",
                },
                {
                    "name": "WideSignal",
                    "startBit": 64,
                    "length": 16,
                    "byteOrder": "little_endian",
                    "signed": False,
                    "factor": 1.0, "offset": 0.0,
                    "minimum": 0.0, "maximum": 65535.0,
                    "unit": "", "presence": "always",
                },
            ],
        }],
    }

    CANFD_DBC_64 = {
        "version": "1.0",
        "messages": [{
            "id": 0x300,
            "name": "CANFDMessage64",
            "dlc": 64,
            "sender": "ECU",
            "signals": [
                {
                    "name": "FirstByte",
                    "startBit": 0,
                    "length": 8,
                    "byteOrder": "little_endian",
                    "signed": False,
                    "factor": 1.0, "offset": 0.0,
                    "minimum": 0.0, "maximum": 255.0,
                    "unit": "", "presence": "always",
                },
                {
                    "name": "LastWord",
                    "startBit": 496,
                    "length": 16,
                    "byteOrder": "little_endian",
                    "signed": False,
                    "factor": 1.0, "offset": 0.0,
                    "minimum": 0.0, "maximum": 65535.0,
                    "unit": "", "presence": "always",
                },
            ],
        }],
    }

    def test_canfd_extract_12_byte_frame(self):
        """Extract signals from a 12-byte CAN-FD frame (DLC code 9)."""
        with AletheiaClient(rts_cores=2) as client:
            client.parse_dbc(self.CANFD_DBC_12)
            data = bytearray(12)
            data[0] = 42          # BaseSignal = 42
            data[8] = 0xCD        # WideSignal low byte
            data[9] = 0xAB        # WideSignal high byte -> 0xABCD = 43981
            result = client.extract_signals(can_id=0x200, dlc=9, data=data)
            assert result.values["BaseSignal"] == 42.0
            assert result.values["WideSignal"] == 43981.0
            assert not result.errors

    def test_canfd_extract_64_byte_frame(self):
        """Extract signals from a 64-byte CAN-FD frame (DLC code 15)."""
        with AletheiaClient(rts_cores=2) as client:
            client.parse_dbc(self.CANFD_DBC_64)
            data = bytearray(64)
            data[0] = 99          # FirstByte = 99
            data[62] = 0x34       # LastWord low byte
            data[63] = 0x12       # LastWord high byte -> 0x1234 = 4660
            result = client.extract_signals(can_id=0x300, dlc=15, data=data)
            assert result.values["FirstByte"] == 99.0
            assert result.values["LastWord"] == 4660.0
            assert not result.errors

    def test_canfd_build_12_byte_frame(self):
        """Build a 12-byte CAN-FD frame from signal values."""
        with AletheiaClient(rts_cores=2) as client:
            client.parse_dbc(self.CANFD_DBC_12)
            frame = client.build_frame(
                can_id=0x200, dlc=9,
                signals={"BaseSignal": 42.0, "WideSignal": 1000.0},
            )
            assert len(frame) == 12
            # Round-trip: extract back
            result = client.extract_signals(can_id=0x200, dlc=9, data=frame)
            assert result.values["BaseSignal"] == 42.0
            assert result.values["WideSignal"] == 1000.0

    def test_canfd_build_64_byte_frame(self):
        """Build a 64-byte CAN-FD frame from signal values."""
        with AletheiaClient(rts_cores=2) as client:
            client.parse_dbc(self.CANFD_DBC_64)
            frame = client.build_frame(
                can_id=0x300, dlc=15,
                signals={"FirstByte": 200.0, "LastWord": 5000.0},
            )
            assert len(frame) == 64
            result = client.extract_signals(can_id=0x300, dlc=15, data=frame)
            assert result.values["FirstByte"] == 200.0
            assert result.values["LastWord"] == 5000.0

    def test_canfd_update_frame(self):
        """Update signals in a CAN-FD frame."""
        with AletheiaClient(rts_cores=2) as client:
            client.parse_dbc(self.CANFD_DBC_12)
            original = client.build_frame(
                can_id=0x200, dlc=9,
                signals={"BaseSignal": 10.0, "WideSignal": 500.0},
            )
            updated = client.update_frame(
                can_id=0x200, dlc=9, frame=original,
                signals={"WideSignal": 9999.0},
            )
            assert len(updated) == 12
            result = client.extract_signals(can_id=0x200, dlc=9, data=updated)
            assert result.values["BaseSignal"] == 10.0  # unchanged
            assert result.values["WideSignal"] == 9999.0  # updated

    def test_canfd_all_valid_dlc_codes(self):
        """All DLC codes 0-15 produce valid frames with correct byte counts."""
        dbc = {
            "version": "1.0",
            "messages": [{
                "id": 0x400,
                "name": "GenericMsg",
                "dlc": 8,
                "sender": "ECU",
                "signals": [{
                    "name": "Sig",
                    "startBit": 0,
                    "length": 8,
                    "byteOrder": "little_endian",
                    "signed": False,
                    "factor": 1.0, "offset": 0.0,
                    "minimum": 0.0, "maximum": 255.0,
                    "unit": "", "presence": "always",
                }],
            }],
        }
        with AletheiaClient(rts_cores=2) as client:
            client.parse_dbc(dbc)
            for dlc_code in range(16):
                nbytes = dlc_to_bytes(dlc_code)
                data = bytearray(nbytes)
                if nbytes > 0:
                    data[0] = dlc_code  # encode DLC code as signal value
                result = client.extract_signals(
                    can_id=0x400, dlc=dlc_code, data=data,
                )
                expected = float(dlc_code) if nbytes > 0 else 0.0
                assert result.values["Sig"] == expected, (
                    f"DLC {dlc_code} ({nbytes} bytes): expected {expected}, "
                    f"got {result.values.get('Sig')}"
                )

    def test_canfd_invalid_dlc_rejected(self):
        """DLC > 15 is rejected by the Python layer."""
        with pytest.raises(ValueError, match="Invalid DLC code"):
            dlc_to_bytes(16)
        with pytest.raises(ValueError, match="Invalid DLC code"):
            dlc_to_bytes(255)

    def test_canfd_byte_count_mismatch(self):
        """Payload byte count must match DLC."""
        with AletheiaClient(rts_cores=2) as client:
            client.parse_dbc(self.CANFD_DBC_12)
            # DLC 9 expects 12 bytes, send 11 — backend rejects the mismatch
            data = bytearray(11)
            with pytest.raises(ProcessError, match="payload length .* does not match DLC"):
                client.extract_signals(can_id=0x200, dlc=9, data=data)

    def test_canfd_ltl_streaming(self):
        """Stream CAN-FD frames with LTL property checking."""
        with AletheiaClient(rts_cores=2) as client:
            client.parse_dbc(self.CANFD_DBC_12)
            client.set_properties([
                Signal("WideSignal").less_than(50000).always().to_dict()
            ])
            client.start_stream()

            # Send frames with WideSignal < 50000 — should pass
            for i in range(5):
                data = bytearray(12)
                data[8] = i  # WideSignal = i (small value)
                resp = client.send_frame(
                    timestamp=i * 1000, can_id=0x200, dlc=9, data=data,
                )
                assert resp["status"] == "ack", f"Frame {i}: {resp}"

            # Send frame with WideSignal = 60000 > 50000 — should violate
            data = bytearray(12)
            data[8] = 0x60  # 0xEA60 = 60000
            data[9] = 0xEA
            resp = client.send_frame(
                timestamp=5000, can_id=0x200, dlc=9, data=data,
            )
            assert resp["status"] == "fails"

            client.end_stream()


class TestNestedMultiplexing:
    """Nested multiplexing: a multiplexor signal that is itself multiplexed.

    DBC layout:
      - Mode: top-level signal, always present (8 bits @ 0)
      - SubMode: present only when Mode == 3 (8 bits @ 8)
      - Detail: present only when SubMode == 7 (16 bits @ 16)

    Detail is two levels deep — its presence requires both Mode == 3 AND
    SubMode == 7. This DBC was rejected by the previous validator
    (MultiplexorNotAlwaysPresent) because SubMode is itself conditional;
    nested-mux support means it's now accepted, and extraction walks the
    chain bottom-up.
    """

    NESTED_DBC = {
        "version": "1.0",
        "messages": [{
            "id": 0x400,
            "name": "Diagnostic",
            "dlc": 8,
            "sender": "ECU",
            "signals": [
                {
                    "name": "Mode",
                    "startBit": 0, "length": 8,
                    "byteOrder": "little_endian", "signed": False,
                    "factor": 1.0, "offset": 0.0,
                    "minimum": 0.0, "maximum": 255.0,
                    "unit": "", "presence": "always",
                },
                {
                    "name": "SubMode",
                    "startBit": 8, "length": 8,
                    "byteOrder": "little_endian", "signed": False,
                    "factor": 1.0, "offset": 0.0,
                    "minimum": 0.0, "maximum": 255.0,
                    "unit": "",
                    "multiplexor": "Mode", "multiplex_values": [3],
                },
                {
                    "name": "Detail",
                    "startBit": 16, "length": 16,
                    "byteOrder": "little_endian", "signed": False,
                    "factor": 1.0, "offset": 0.0,
                    "minimum": 0.0, "maximum": 65535.0,
                    "unit": "",
                    "multiplexor": "SubMode", "multiplex_values": [7],
                },
            ],
        }],
    }

    def test_nested_mux_dbc_validates_clean(self) -> None:
        """Nested mux is no longer rejected by validation."""
        with AletheiaClient() as client:
            result = client.validate_dbc(self.NESTED_DBC)
            assert result["has_errors"] is False
            assert result["issues"] == []

    def test_full_chain_match_extracts_leaf(self) -> None:
        """Mode==3 and SubMode==7 → Detail extracts."""
        with AletheiaClient() as client:
            client.parse_dbc(self.NESTED_DBC)
            data = bytearray([3, 7, 0xCD, 0xAB, 0, 0, 0, 0])  # Detail = 0xABCD = 43981
            result = client.extract_signals(can_id=0x400, dlc=8, data=data)
            assert result.values["Mode"] == 3.0
            assert result.values["SubMode"] == 7.0
            assert result.values["Detail"] == 43981.0
            assert result.absent == ()
            assert result.errors == {}

    def test_inner_mismatch_marks_leaf_absent(self) -> None:
        """Mode==3 but SubMode==5 → SubMode extracts, Detail absent."""
        with AletheiaClient() as client:
            client.parse_dbc(self.NESTED_DBC)
            data = bytearray([3, 5, 0xCD, 0xAB, 0, 0, 0, 0])
            result = client.extract_signals(can_id=0x400, dlc=8, data=data)
            assert result.values["Mode"] == 3.0
            assert result.values["SubMode"] == 5.0
            assert "Detail" in result.absent
            assert "Detail" not in result.values

    def test_outer_mismatch_marks_inner_and_leaf_absent(self) -> None:
        """Mode==2 → both SubMode and Detail are absent."""
        with AletheiaClient() as client:
            client.parse_dbc(self.NESTED_DBC)
            data = bytearray([2, 7, 0xCD, 0xAB, 0, 0, 0, 0])
            result = client.extract_signals(can_id=0x400, dlc=8, data=data)
            assert result.values["Mode"] == 2.0
            assert "SubMode" in result.absent
            assert "Detail" in result.absent
            assert "SubMode" not in result.values
            assert "Detail" not in result.values

    def test_mux_cycle_rejected_by_validator(self) -> None:
        """A self-referential mux chain is rejected as multiplexor_cycle."""
        cyclic = {
            "version": "1.0",
            "messages": [{
                "id": 0x500,
                "name": "Cyclic",
                "dlc": 8,
                "sender": "ECU",
                "signals": [
                    {
                        "name": "A",
                        "startBit": 0, "length": 8,
                        "byteOrder": "little_endian", "signed": False,
                        "factor": 1.0, "offset": 0.0,
                        "minimum": 0.0, "maximum": 255.0,
                        "unit": "",
                        "multiplexor": "B", "multiplex_values": [1],
                    },
                    {
                        "name": "B",
                        "startBit": 8, "length": 8,
                        "byteOrder": "little_endian", "signed": False,
                        "factor": 1.0, "offset": 0.0,
                        "minimum": 0.0, "maximum": 255.0,
                        "unit": "",
                        "multiplexor": "A", "multiplex_values": [1],
                    },
                ],
            }],
        }
        with AletheiaClient() as client:
            result = client.validate_dbc(cyclic)
            assert result["has_errors"] is True
            codes = [i["code"] for i in result["issues"]]
            assert "multiplexor_cycle" in codes
