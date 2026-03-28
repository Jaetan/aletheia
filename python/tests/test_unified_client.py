"""Tests for the unified AletheiaClient.

Tests that the unified client can:
1. Parse DBC and extract signals
2. Build frames from signal values
3. Update frames with new signal values
4. Stream frames with LTL property checking
5. Mix signal operations while streaming
"""

import json
from pathlib import Path

import pytest

from aletheia import AletheiaClient, Signal, dlc_to_bytes
from aletheia.client._types import ProcessError
from aletheia.dbc_converter import dbc_to_json


@pytest.fixture
def demo_dbc() -> dict:
    """Load the demo vehicle DBC."""
    dbc_path = Path(__file__).parent.parent.parent / "examples" / "demo" / "vehicle.dbc"
    return dbc_to_json(str(dbc_path))


@pytest.fixture
def simple_dbc() -> dict:
    """Create a simple DBC for testing."""
    return {
        "version": "1.0",
        "messages": [
            {
                "id": 256,
                "name": "TestMessage",
                "dlc": 8,
                "sender": "ECU",
                "signals": [
                    {
                        "name": "TestSignal",
                        "startBit": 0,
                        "length": 16,
                        "byteOrder": "little_endian",
                        "signed": False,
                        "factor": 1.0,
                        "offset": 0.0,
                        "minimum": 0.0,
                        "maximum": 65535.0,
                        "unit": "",
                        "presence": "always"
                    }
                ]
            }
        ]
    }


class TestAletheiaClientBasics:
    """Basic functionality tests."""

    def test_parse_dbc(self, simple_dbc: dict) -> None:
        """Test DBC parsing."""
        with AletheiaClient() as client:
            response = client.parse_dbc(simple_dbc)
            assert response.get("status") == "success"

    def test_extract_signals(self, simple_dbc: dict) -> None:
        """Test signal extraction."""
        with AletheiaClient() as client:
            client.parse_dbc(simple_dbc)
            result = client.extract_signals(can_id=256, dlc=8, data=bytearray([100, 0, 0, 0, 0, 0, 0, 0]))
            assert result.get("TestSignal") == 100.0

    def test_build_frame(self, simple_dbc: dict) -> None:
        """Test frame building."""
        with AletheiaClient() as client:
            client.parse_dbc(simple_dbc)
            frame = client.build_frame(can_id=256, signals={"TestSignal": 1000.0})
            assert len(frame) == 8
            # Verify by extracting
            result = client.extract_signals(can_id=256, dlc=8, data=frame)
            assert result.get("TestSignal") == 1000.0

    def test_update_frame(self, simple_dbc: dict) -> None:
        """Test frame updating."""
        with AletheiaClient() as client:
            client.parse_dbc(simple_dbc)
            original = bytearray([50, 0, 0, 0, 0, 0, 0, 0])
            updated = client.update_frame(can_id=256, dlc=8, frame=original, signals={"TestSignal": 200.0})
            assert len(updated) == 8
            # Verify
            result = client.extract_signals(can_id=256, dlc=8, data=updated)
            assert result.get("TestSignal") == 200.0


class TestAletheiaClientStreaming:
    """Streaming LTL tests."""

    def test_streaming_no_violation(self, simple_dbc: dict) -> None:
        """Test streaming without violations."""
        with AletheiaClient() as client:
            client.parse_dbc(simple_dbc)
            client.set_properties([
                Signal("TestSignal").less_than(1000).always().to_dict()
            ])
            client.start_stream()

            # Send frames that don't violate
            for i in range(10):
                response = client.send_frame(
                    timestamp=i * 1000,
                    can_id=256,
                    dlc=8,
                    data=bytearray([i * 10, 0, 0, 0, 0, 0, 0, 0])  # Values 0-90
                )
                assert response.get("status") == "ack"

            response = client.end_stream()
            assert response.get("status") == "complete"

    def test_streaming_with_violation(self, simple_dbc: dict) -> None:
        """Test streaming with a violation."""
        with AletheiaClient() as client:
            client.parse_dbc(simple_dbc)
            client.set_properties([
                Signal("TestSignal").less_than(100).always().to_dict()
            ])
            client.start_stream()

            # Send frame that violates (value = 200 > 100)
            response = client.send_frame(
                timestamp=1000,
                can_id=256,
                dlc=8,
                data=bytearray([200, 0, 0, 0, 0, 0, 0, 0])
            )
            assert response.get("status") == "violation"

            client.end_stream()


class TestAletheiaClientMixedOperations:
    """Test mixing signal operations with streaming."""

    def test_extract_while_streaming(self, simple_dbc: dict) -> None:
        """Test that extract_signals works while streaming."""
        with AletheiaClient() as client:
            client.parse_dbc(simple_dbc)
            client.set_properties([
                Signal("TestSignal").less_than(1000).always().to_dict()
            ])
            client.start_stream()

            # Send a frame
            client.send_frame(timestamp=1000, can_id=256, dlc=8, data=bytearray([50, 0, 0, 0, 0, 0, 0, 0]))

            # Extract signals while streaming (should work!)
            result = client.extract_signals(can_id=256, dlc=8, data=bytearray([100, 0, 0, 0, 0, 0, 0, 0]))
            assert result.get("TestSignal") == 100.0

            # Continue streaming
            client.send_frame(timestamp=2000, can_id=256, dlc=8, data=bytearray([60, 0, 0, 0, 0, 0, 0, 0]))

            client.end_stream()

    def test_update_while_streaming(self, simple_dbc: dict) -> None:
        """Test that update_frame works while streaming."""
        with AletheiaClient() as client:
            client.parse_dbc(simple_dbc)
            client.set_properties([
                Signal("TestSignal").less_than(1000).always().to_dict()
            ])
            client.start_stream()

            # Update a frame while streaming
            original = bytearray([50, 0, 0, 0, 0, 0, 0, 0])
            updated = client.update_frame(can_id=256, dlc=8, frame=original, signals={"TestSignal": 75.0})

            # Send the updated frame
            response = client.send_frame(timestamp=1000, can_id=256, dlc=8, data=updated)
            assert response.get("status") == "ack"

            client.end_stream()

    def test_build_while_streaming(self, simple_dbc: dict) -> None:
        """Test that build_frame works while streaming."""
        with AletheiaClient() as client:
            client.parse_dbc(simple_dbc)
            client.set_properties([
                Signal("TestSignal").less_than(1000).always().to_dict()
            ])
            client.start_stream()

            # Build a frame while streaming
            frame = client.build_frame(can_id=256, signals={"TestSignal": 500.0})

            # Send it
            response = client.send_frame(timestamp=1000, can_id=256, dlc=8, data=frame)
            assert response.get("status") == "ack"

            client.end_stream()


class TestAletheiaClientLifecycle:
    """Test GHC RTS lifecycle with multiple sequential clients."""

    def test_sequential_clients(self, simple_dbc: dict) -> None:
        """Multiple sequential clients in one process should work."""
        for _ in range(3):
            with AletheiaClient() as client:
                response = client.parse_dbc(simple_dbc)
                assert response.get("status") == "success"

    def test_restart_stream(self, simple_dbc: dict) -> None:
        """Stream can be restarted after end_stream."""
        with AletheiaClient() as client:
            client.parse_dbc(simple_dbc)
            client.set_properties(
                [Signal("TestSignal").less_than(65535).always().to_dict()]
            )

            # First stream
            client.start_stream()
            client.send_frame(timestamp=0, can_id=256, dlc=8, data=bytearray([1, 0, 0, 0, 0, 0, 0, 0]))
            client.end_stream()

            # Second stream (same client, same DBC)
            client.start_stream()
            resp = client.send_frame(timestamp=1, can_id=256, dlc=8, data=bytearray([2, 0, 0, 0, 0, 0, 0, 0]))
            assert resp.get("status") == "ack"
            client.end_stream()


    def test_threaded_isolation(self) -> None:
        """Two clients in separate threads produce correct independent results.

        Runs in a subprocess so the GHC RTS is initialized fresh with
        ``-N2`` (two capabilities).  Both threads send the same frames
        (TestSignal = 200) but with different thresholds: thread A
        expects violation (< 100), thread B expects no violation (< 1000).
        A Barrier ensures both threads are inside the send_frame loop
        simultaneously, so the GHC RTS genuinely runs in parallel.
        """
        import subprocess
        import sys
        import textwrap

        script = textwrap.dedent("""\
            import json, sys, threading
            from aletheia import AletheiaClient, Signal

            DBC = {
                "version": "1.0",
                "messages": [{
                    "id": 256, "name": "TestMessage", "dlc": 8,
                    "sender": "ECU",
                    "signals": [{
                        "name": "TestSignal", "startBit": 0, "length": 16,
                        "byteOrder": "little_endian", "signed": False,
                        "factor": 1.0, "offset": 0.0,
                        "minimum": 0.0, "maximum": 65535.0,
                        "unit": "", "presence": "always"
                    }]
                }]
            }
            FRAMES = [
                (i * 1000, 256, 8, bytearray([200, 0, 0, 0, 0, 0, 0, 0]))
                for i in range(20)
            ]
            results = {"A": None, "B": None}
            errors = []
            barrier = threading.Barrier(2, timeout=5)

            def run_client(name, threshold):
                try:
                    with AletheiaClient(rts_cores=2) as client:
                        client.parse_dbc(DBC)
                        client.set_properties([
                            Signal("TestSignal").less_than(threshold).always().to_dict()
                        ])
                        client.start_stream()
                        barrier.wait()
                        for ts, cid, dlc, data in FRAMES:
                            resp = client.send_frame(timestamp=ts, can_id=cid, dlc=dlc, data=data)
                            if resp.get("status") == "violation":
                                results[name] = "violation"
                                client.end_stream()
                                return
                        resp = client.end_stream()
                        results[name] = resp.get("status")
                except Exception as e:
                    errors.append(str(e))

            t_a = threading.Thread(target=run_client, args=("A", 100))
            t_b = threading.Thread(target=run_client, args=("B", 1000))
            t_a.start()
            t_b.start()
            t_a.join(timeout=10)
            t_b.join(timeout=10)

            out = {"results": results, "errors": errors}
            print(json.dumps(out))
            sys.exit(0 if not errors else 1)
        """)
        result = subprocess.run(
            [sys.executable, "-c", script],
            capture_output=True, text=True, timeout=15,
        )
        assert result.returncode == 0, (
            f"Subprocess failed:\nstdout: {result.stdout}\nstderr: {result.stderr}"
        )
        out = json.loads(result.stdout)
        assert not out["errors"], f"Thread raised: {out['errors']}"
        assert out["results"]["A"] == "violation", (
            f"Thread A should violate, got {out['results']['A']}"
        )
        assert out["results"]["B"] == "complete", (
            f"Thread B should complete clean, got {out['results']['B']}"
        )


class TestAletheiaClientWithDemoDBC:
    """Tests using the demo vehicle DBC."""

    def test_vehicle_speed_extraction(self, demo_dbc: dict) -> None:
        """Test extracting vehicle speed from demo DBC."""
        with AletheiaClient() as client:
            client.parse_dbc(demo_dbc)

            # Build a frame with speed = 72 kph
            frame = client.build_frame(can_id=0x100, signals={"VehicleSpeed": 72.0})

            # Extract and verify
            result = client.extract_signals(can_id=0x100, dlc=8, data=frame)
            assert abs(result.get("VehicleSpeed") - 72.0) < 0.01

    def test_fault_injection_single_session(self, demo_dbc: dict) -> None:
        """Test fault injection in a single streaming session."""
        with AletheiaClient() as client:
            client.parse_dbc(demo_dbc)
            client.set_properties([
                Signal("VehicleSpeed").less_than(120).always().to_dict()
            ])
            client.start_stream()

            # Send normal frames
            for i in range(5):
                frame = client.build_frame(can_id=0x100, signals={"VehicleSpeed": 50.0 + i})
                response = client.send_frame(timestamp=i * 100000, can_id=0x100, dlc=8, data=frame)
                assert response.get("status") == "ack"

            # Inject fault: speed = 130 kph (exceeds 120 limit)
            fault_frame = client.build_frame(can_id=0x100, signals={"VehicleSpeed": 130.0})
            response = client.send_frame(timestamp=500000, can_id=0x100, dlc=8, data=fault_frame)
            assert response.get("status") == "violation"

            client.end_stream()


class TestStateMachineErrors:
    """Test that invalid state transitions produce correct errors."""

    def test_extract_signals_without_dbc(self) -> None:
        """extract_signals before parse_dbc raises ProcessError."""
        with AletheiaClient() as client:
            with pytest.raises(ProcessError, match="DBC not loaded"):
                client.extract_signals(can_id=256, dlc=8, data=bytearray(8))

    def test_build_frame_without_dbc(self) -> None:
        """build_frame before parse_dbc raises ProcessError."""
        with AletheiaClient() as client:
            with pytest.raises(ProcessError, match="DBC not loaded"):
                client.build_frame(can_id=256, signals={"Sig": 1.0})

    def test_send_frame_without_stream(self, simple_dbc: dict) -> None:
        """send_frame before start_stream returns error response."""
        with AletheiaClient() as client:
            client.parse_dbc(simple_dbc)
            client.set_properties([
                Signal("TestSignal").less_than(1000).always().to_dict()
            ])
            response = client.send_frame(
                timestamp=0, can_id=256, dlc=8, data=bytearray(8),
            )
            assert response["status"] == "error"

    def test_end_stream_without_start(self, simple_dbc: dict) -> None:
        """end_stream without start_stream returns error response."""
        with AletheiaClient() as client:
            client.parse_dbc(simple_dbc)
            response = client.end_stream()
            assert response["status"] == "error"


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
            with pytest.raises(ProcessError, match="byte count doesn't match DLC"):
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
            assert resp["status"] == "violation"

            client.end_stream()
