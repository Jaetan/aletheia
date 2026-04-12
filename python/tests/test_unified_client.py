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
from aletheia.client._response_parsers import parse_event_response
from aletheia.client._types import ProcessError, ProtocolError
from aletheia.dbc_converter import dbc_to_json
from aletheia.protocols import DBCDefinition


@pytest.fixture
def demo_dbc() -> DBCDefinition:
    """Load the demo vehicle DBC."""
    dbc_path = Path(__file__).parent.parent.parent / "examples" / "demo" / "vehicle.dbc"
    return dbc_to_json(str(dbc_path))


@pytest.fixture
def simple_dbc() -> DBCDefinition:
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

    def test_parse_dbc(self, simple_dbc: DBCDefinition) -> None:
        """Test DBC parsing."""
        with AletheiaClient() as client:
            response = client.parse_dbc(simple_dbc)
            assert response.get("status") == "success"

    def test_extract_signals(self, simple_dbc: DBCDefinition) -> None:
        """Test signal extraction."""
        with AletheiaClient() as client:
            client.parse_dbc(simple_dbc)
            result = client.extract_signals(can_id=256, dlc=8, data=bytearray([100, 0, 0, 0, 0, 0, 0, 0]))
            assert result.get("TestSignal") == 100.0

    def test_build_frame(self, simple_dbc: DBCDefinition) -> None:
        """Test frame building."""
        with AletheiaClient() as client:
            client.parse_dbc(simple_dbc)
            frame = client.build_frame(can_id=256, dlc=8, signals={"TestSignal": 1000.0})
            assert len(frame) == 8
            # Verify by extracting
            result = client.extract_signals(can_id=256, dlc=8, data=frame)
            assert result.get("TestSignal") == 1000.0

    def test_update_frame(self, simple_dbc: DBCDefinition) -> None:
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

    def test_streaming_no_violation(self, simple_dbc: DBCDefinition) -> None:
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

    def test_streaming_with_violation(self, simple_dbc: DBCDefinition) -> None:
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
            assert response.get("status") == "fails"

            client.end_stream()


class TestAletheiaClientMixedOperations:
    """Test mixing signal operations with streaming."""

    def test_extract_while_streaming(self, simple_dbc: DBCDefinition) -> None:
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

    def test_update_while_streaming(self, simple_dbc: DBCDefinition) -> None:
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

    def test_build_while_streaming(self, simple_dbc: DBCDefinition) -> None:
        """Test that build_frame works while streaming."""
        with AletheiaClient() as client:
            client.parse_dbc(simple_dbc)
            client.set_properties([
                Signal("TestSignal").less_than(1000).always().to_dict()
            ])
            client.start_stream()

            # Build a frame while streaming
            frame = client.build_frame(can_id=256, dlc=8, signals={"TestSignal": 500.0})

            # Send it
            response = client.send_frame(timestamp=1000, can_id=256, dlc=8, data=frame)
            assert response.get("status") == "ack"

            client.end_stream()


class TestAletheiaClientLifecycle:
    """Test GHC RTS lifecycle with multiple sequential clients."""

    def test_sequential_clients(self, simple_dbc: DBCDefinition) -> None:
        """Multiple sequential clients in one process should work."""
        for _ in range(3):
            with AletheiaClient() as client:
                response = client.parse_dbc(simple_dbc)
                assert response.get("status") == "success"

    def test_double_close_is_safe(self, simple_dbc: DBCDefinition) -> None:
        """Calling close() twice on the same client must be a no-op.

        ``_client.close()`` clears ``_lib`` and ``_state`` in a finally block
        and guards on ``None``. A double-close should not crash or double-free
        the FFI state pointer. Mirrors Go's ``TestDoubleClose``.
        """
        client = AletheiaClient()
        client.__enter__()
        response = client.parse_dbc(simple_dbc)
        assert response.get("status") == "success"

        client.close()
        client.close()  # Second close must be safe.
        assert client._state is None
        assert client._lib is None

    def test_use_after_close_raises(self, simple_dbc: DBCDefinition) -> None:
        """Operations on a closed client must raise, not crash.

        After ``close()`` both ``_lib`` and ``_state`` are ``None``.
        ``_send_command`` must detect the uninitialized state and raise
        ``ProcessError``; any other behavior (crash, silent no-op, use of
        a dangling state pointer) would be a serious safety bug.
        Mirrors Go's ``TestUseAfterClose``.
        """
        client = AletheiaClient()
        client.__enter__()
        client.parse_dbc(simple_dbc)
        client.close()

        with pytest.raises(ProcessError, match="not initialized"):
            client.parse_dbc(simple_dbc)

    def test_exit_then_reenter_raises(self, simple_dbc: DBCDefinition) -> None:
        """After ``__exit__`` via ``with`` block, the client must not be reusable.

        Unlike ``with`` blocks that create fresh clients, reusing the
        same instance after ``__exit__`` should raise. This guards against
        accidental resurrection of a closed client in user code.
        """
        client = AletheiaClient()
        with client:
            client.parse_dbc(simple_dbc)

        # After the `with` block, the client is closed — any operation raises.
        with pytest.raises(ProcessError, match="not initialized"):
            client.parse_dbc(simple_dbc)

        # Double-close on the already-closed client must also be safe.
        client.close()

    def test_in_process_concurrent_clients(self, simple_dbc: DBCDefinition) -> None:
        """Multiple concurrent clients in the same pytest process work correctly.

        Unlike ``test_threaded_isolation`` (which runs in a subprocess with
        ``rts_cores=2`` for genuine parallelism), this test runs directly
        inside the pytest process with the default single-capability RTS.
        The goal is to exercise the in-process concurrency path: multiple
        ``AletheiaClient`` instances with independent FFI state pointers,
        concurrent ``aletheia_process`` calls serialised through the GHC
        scheduler, and independent streaming verdicts.

        Three client threads each stream the same frame payload
        (``TestSignal = 200``) but with different LTL thresholds:

        * **Thread A** — ``TestSignal < 100`` → expected ``fails`` (200 ≥ 100)
        * **Thread B** — ``TestSignal < 500`` → expected ``fails`` (200 ≥ ... wait no, 200 < 500 → holds)
        * **Thread C** — ``TestSignal < 1000`` → expected ``complete`` (clean)

        The threads synchronise through a ``threading.Barrier`` so they're
        all inside the streaming loop simultaneously, which forces the FFI
        layer to juggle three concurrent state pointers. If any thread
        leaks state into another (shared global, stale cache, unprotected
        mutation), the verdicts will be wrong.
        """
        import threading

        # Rewrite threshold inside the property for each thread.
        def make_property(threshold: int) -> dict:
            return Signal("TestSignal").less_than(threshold).always().to_dict()

        frames = [(i * 1000, 256, 8, bytearray([200, 0, 0, 0, 0, 0, 0, 0])) for i in range(10)]
        results: dict[str, str | None] = {"A": None, "B": None, "C": None}
        errors: list[str] = []
        barrier = threading.Barrier(3, timeout=10)

        def run_client(name: str, threshold: int) -> None:
            try:
                with AletheiaClient() as client:
                    client.parse_dbc(simple_dbc)
                    client.set_properties([make_property(threshold)])
                    client.start_stream()
                    barrier.wait()  # Ensure all three threads are live simultaneously.
                    violated = False
                    for ts, cid, dlc, data in frames:
                        resp = client.send_frame(
                            timestamp=ts, can_id=cid, dlc=dlc, data=data
                        )
                        if resp.get("status") == "fails":
                            violated = True
                            results[name] = "fails"
                            client.end_stream()
                            return
                    if not violated:
                        resp = client.end_stream()
                        results[name] = resp.get("status")
            except Exception as e:  # pylint: disable=broad-exception-caught
                errors.append(f"{name}: {e}")

        threads = [
            threading.Thread(target=run_client, args=("A", 100)),
            threading.Thread(target=run_client, args=("B", 500)),
            threading.Thread(target=run_client, args=("C", 1000)),
        ]
        for t in threads:
            t.start()
        for t in threads:
            t.join(timeout=15)

        assert not errors, f"Thread errors: {errors}"
        # A: 200 is not < 100 → fails on first frame
        assert results["A"] == "fails", f"Thread A should fail, got {results['A']}"
        # B: 200 < 500 holds for every frame → complete
        assert results["B"] == "complete", f"Thread B should complete, got {results['B']}"
        # C: 200 < 1000 holds for every frame → complete
        assert results["C"] == "complete", f"Thread C should complete, got {results['C']}"

    def test_restart_stream(self, simple_dbc: DBCDefinition) -> None:
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
                            if resp.get("status") == "fails":
                                results[name] = "fails"
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
        assert out["results"]["A"] == "fails", (
            f"Thread A should violate, got {out['results']['A']}"
        )
        assert out["results"]["B"] == "complete", (
            f"Thread B should complete clean, got {out['results']['B']}"
        )


class TestAletheiaClientWithDemoDBC:
    """Tests using the demo vehicle DBC."""

    def test_vehicle_speed_extraction(self, demo_dbc: DBCDefinition) -> None:
        """Test extracting vehicle speed from demo DBC."""
        with AletheiaClient() as client:
            client.parse_dbc(demo_dbc)

            # Build a frame with speed = 72 kph
            frame = client.build_frame(can_id=0x100, dlc=8, signals={"VehicleSpeed": 72.0})

            # Extract and verify
            result = client.extract_signals(can_id=0x100, dlc=8, data=frame)
            assert abs(result.get("VehicleSpeed") - 72.0) < 0.01

    def test_fault_injection_single_session(self, demo_dbc: DBCDefinition) -> None:
        """Test fault injection in a single streaming session."""
        with AletheiaClient() as client:
            client.parse_dbc(demo_dbc)
            client.set_properties([
                Signal("VehicleSpeed").less_than(120).always().to_dict()
            ])
            client.start_stream()

            # Send normal frames
            for i in range(5):
                frame = client.build_frame(can_id=0x100, dlc=8, signals={"VehicleSpeed": 50.0 + i})
                response = client.send_frame(timestamp=i * 100000, can_id=0x100, dlc=8, data=frame)
                assert response.get("status") == "ack"

            # Inject fault: speed = 130 kph (exceeds 120 limit)
            fault_frame = client.build_frame(can_id=0x100, dlc=8, signals={"VehicleSpeed": 130.0})
            response = client.send_frame(timestamp=500000, can_id=0x100, dlc=8, data=fault_frame)
            assert response.get("status") == "fails"

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
                client.build_frame(can_id=256, dlc=8, signals={"Sig": 1.0})

    def test_send_frame_without_stream(self, simple_dbc: DBCDefinition) -> None:
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

    def test_end_stream_without_start(self, simple_dbc: DBCDefinition) -> None:
        """end_stream without start_stream returns error response."""
        with AletheiaClient() as client:
            client.parse_dbc(simple_dbc)
            response = client.end_stream()
            assert response["status"] == "error"

    def test_end_stream_unresolved_verdict(self, simple_dbc: DBCDefinition) -> None:
        """LTL atomic whose signal is never observed finalizes to Unresolved.

        Path G: the Agda coalgebra's three-valued Kleene ``finalizeL`` returns
        ``Unsure`` for unresolved atomic predicates at end-of-stream. This is
        exposed as ``status="unresolved"`` in the JSON protocol — a distinct
        verdict from ``"fails"``.
        """
        with AletheiaClient() as client:
            client.parse_dbc(simple_dbc)
            client.set_properties([
                # Predicate targets a signal that is not in simple_dbc —
                # therefore never evaluated on any frame, so its verdict stays
                # Unknown at end-of-stream.
                Signal("UnknownSignal").less_than(100).always().to_dict()
            ])
            client.start_stream()
            # Send an unrelated frame that carries TestSignal only.
            client.send_frame(
                timestamp=1000, can_id=256, dlc=8,
                data=bytearray([10, 0, 0, 0, 0, 0, 0, 0]),
            )
            end_resp = client.end_stream()
            assert end_resp["status"] == "complete"
            results = end_resp["results"]
            assert len(results) == 1
            assert results[0]["status"] == "unresolved"
            assert "never resolved" in results[0].get("reason", "")

    def test_send_frame_non_monotonic_timestamp(self, simple_dbc: DBCDefinition) -> None:
        """Backward timestamps are rejected by Agda with handler_non_monotonic_timestamp.

        Metric LTL operators compute elapsed time via truncated subtraction (∸),
        which would silently produce wrong verdicts on regressing timestamps.
        Agda's handleDataFrame refuses such frames — this is the single source of
        truth across all language bindings.
        """
        with AletheiaClient() as client:
            client.parse_dbc(simple_dbc)
            client.set_properties([
                Signal("TestSignal").less_than(1000).always().to_dict()
            ])
            client.start_stream()

            # First frame at t=5000 µs — accepted.
            ok = client.send_frame(
                timestamp=5000, can_id=256, dlc=8,
                data=bytearray([10, 0, 0, 0, 0, 0, 0, 0]),
            )
            assert ok.get("status") == "ack"

            # Regressing to t=4999 µs — rejected.
            err = client.send_frame(
                timestamp=4999, can_id=256, dlc=8,
                data=bytearray([11, 0, 0, 0, 0, 0, 0, 0]),
            )
            assert err["status"] == "error"
            assert err["code"] == "handler_non_monotonic_timestamp"

            # Same-timestamp frames (≥, not >) are accepted.
            eq = client.send_frame(
                timestamp=5000, can_id=256, dlc=8,
                data=bytearray([12, 0, 0, 0, 0, 0, 0, 0]),
            )
            assert eq.get("status") == "ack"

            # Anchor is unchanged after rejection — next ≥ 5000 still accepted.
            fwd = client.send_frame(
                timestamp=6000, can_id=256, dlc=8,
                data=bytearray([13, 0, 0, 0, 0, 0, 0, 0]),
            )
            assert fwd.get("status") == "ack"

            client.end_stream()


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


class TestSendErrorRemote:
    """Tests for send_error() and send_remote() response parsing."""

    def test_send_error_ack_during_stream(self, simple_dbc: DBCDefinition) -> None:
        """send_error returns ack when streaming."""
        with AletheiaClient() as client:
            client.parse_dbc(simple_dbc)
            client.set_properties([])
            client.start_stream()
            response = client.send_error(timestamp=1000)
            assert response["status"] == "ack"
            client.end_stream()

    def test_send_error_outside_stream_acks(self, simple_dbc: DBCDefinition) -> None:
        """send_error outside streaming still acks (no LTL to evaluate)."""
        with AletheiaClient() as client:
            client.parse_dbc(simple_dbc)
            response = client.send_error(timestamp=1000)
            assert response["status"] == "ack"

    def test_send_remote_ack_during_stream(self, simple_dbc: DBCDefinition) -> None:
        """send_remote returns ack when streaming."""
        with AletheiaClient() as client:
            client.parse_dbc(simple_dbc)
            client.set_properties([])
            client.start_stream()
            response = client.send_remote(timestamp=1000, can_id=256)
            assert response["status"] == "ack"
            client.end_stream()

    def test_send_remote_outside_stream_acks(self, simple_dbc: DBCDefinition) -> None:
        """send_remote outside streaming still acks (no LTL to evaluate)."""
        with AletheiaClient() as client:
            client.parse_dbc(simple_dbc)
            response = client.send_remote(timestamp=1000, can_id=256)
            assert response["status"] == "ack"

    def test_send_error_negative_timestamp_rejected(self) -> None:
        """send_error rejects negative timestamps."""
        with AletheiaClient() as client:
            with pytest.raises(ValueError, match="non-negative"):
                client.send_error(timestamp=-1)

    def test_send_remote_negative_timestamp_rejected(self) -> None:
        """send_remote rejects negative timestamps."""
        with AletheiaClient() as client:
            with pytest.raises(ValueError, match="non-negative"):
                client.send_remote(timestamp=-1, can_id=256)

    def test_send_remote_invalid_can_id_rejected(self) -> None:
        """send_remote rejects out-of-range standard CAN IDs."""
        with AletheiaClient() as client:
            with pytest.raises(ValueError, match="Invalid"):
                client.send_remote(timestamp=1000, can_id=0x800)

    def test_send_remote_extended_invalid_can_id_rejected(self) -> None:
        """send_remote rejects out-of-range extended CAN IDs."""
        with AletheiaClient() as client:
            with pytest.raises(ValueError, match="Invalid"):
                client.send_remote(timestamp=1000, can_id=0x20000000, extended=True)

    def test_send_error_error_response_raises_protocol_error(self) -> None:
        """parse_event_response raises ProtocolError for error_event errors."""
        with pytest.raises(ProtocolError, match="error_event failed"):
            parse_event_response(
                {"status": "error", "message": "test error", "code": "test_code"},
                "error_event",
                1000,
            )

    def test_send_remote_error_response_raises_protocol_error(self) -> None:
        """parse_event_response raises ProtocolError for remote_event errors."""
        with pytest.raises(ProtocolError, match="remote_event failed") as exc_info:
            parse_event_response(
                {"status": "error", "message": "remote rejected", "code": "handler_err"},
                "remote_event",
                1000,
            )
        assert exc_info.value.code == "handler_err"

    def test_send_remote_extended(self, simple_dbc: DBCDefinition) -> None:
        """send_remote with extended=True accepts 29-bit IDs."""
        with AletheiaClient() as client:
            client.parse_dbc(simple_dbc)
            client.set_properties([])
            client.start_stream()
            response = client.send_remote(
                timestamp=1000, can_id=0x1FFFFFFF, extended=True,
            )
            assert response["status"] == "ack"
            client.end_stream()

    def test_send_error_backward_timestamp_accepted(self, simple_dbc: DBCDefinition) -> None:
        """send_error with a backward timestamp is accepted.

        Error frames carry no payload and do not advance the monotonicity
        anchor in the Agda core.  This verifies that the ack path works
        and that XB5 (ProtocolError on non-ack) does not fire for
        legitimate ack responses.
        """
        with AletheiaClient() as client:
            client.parse_dbc(simple_dbc)
            client.set_properties([
                Signal("TestSignal").less_than(1000).always().to_dict(),
            ])
            client.start_stream()
            client.send_frame(
                timestamp=5000, can_id=256, dlc=8,
                data=bytearray([10, 0, 0, 0, 0, 0, 0, 0]),
            )
            # Error events don't participate in data-frame monotonicity.
            resp = client.send_error(timestamp=4000)
            assert resp["status"] == "ack"
            client.end_stream()

    def test_send_remote_backward_timestamp_accepted(self, simple_dbc: DBCDefinition) -> None:
        """send_remote with a backward timestamp is accepted.

        Remote frames carry no payload and do not advance the monotonicity
        anchor in the Agda core.  This verifies that the ack path works
        and that XB5 (ProtocolError on non-ack) does not fire for
        legitimate ack responses.
        """
        with AletheiaClient() as client:
            client.parse_dbc(simple_dbc)
            client.set_properties([
                Signal("TestSignal").less_than(1000).always().to_dict(),
            ])
            client.start_stream()
            client.send_frame(
                timestamp=5000, can_id=256, dlc=8,
                data=bytearray([10, 0, 0, 0, 0, 0, 0, 0]),
            )
            # Remote events don't participate in data-frame monotonicity.
            resp = client.send_remote(timestamp=4000, can_id=256)
            assert resp["status"] == "ack"
            client.end_stream()


class TestFormatDBC:
    """Tests for format_dbc() round-trip."""

    def test_format_dbc_round_trip(self, simple_dbc: DBCDefinition) -> None:
        """Parsing then formatting a DBC preserves message structure."""
        with AletheiaClient() as client:
            client.parse_dbc(simple_dbc)
            result = client.format_dbc()
            assert "messages" in result
            msgs = result["messages"]
            assert len(msgs) == 1
            assert msgs[0]["name"] == "TestMessage"
            assert msgs[0]["id"] == 256
            assert len(msgs[0]["signals"]) == 1
            assert msgs[0]["signals"][0]["name"] == "TestSignal"

    def test_format_dbc_without_parse_raises(self) -> None:
        """format_dbc before parse_dbc returns an error."""
        with AletheiaClient() as client:
            with pytest.raises(ProtocolError):
                client.format_dbc()


class TestRTSState:
    """Unit tests for GHC RTS reference counting."""

    def test_refcount_increments_on_enter(self) -> None:
        """Each client increments the RTS reference count."""
        from aletheia.client._ffi import RTSState
        initial = RTSState.refcount
        with AletheiaClient():
            assert RTSState.refcount == initial + 1
        assert RTSState.refcount == initial

    def test_release_does_not_go_negative(self) -> None:
        """release() when refcount is 0 stays at 0."""
        from aletheia.client._ffi import RTSState
        saved = RTSState.refcount
        RTSState.refcount = 0
        RTSState.release()
        assert RTSState.refcount == 0
        RTSState.refcount = saved

    def test_rts_cores_mismatch_warns(self) -> None:
        """Second client with different rts_cores emits a warning."""
        with AletheiaClient(rts_cores=1):
            with pytest.warns(UserWarning, match="already initialized"):
                with AletheiaClient(rts_cores=4):
                    pass
