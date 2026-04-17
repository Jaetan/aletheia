"""Core tests for the unified AletheiaClient.

Covers basic operations, streaming, mixed signal/streaming flows, the
client lifecycle (close, restart, threading), and state-machine error
paths.  Sibling files split out:

* ``test_unified_client_canfd_mux.py`` — CAN-FD frames and nested mux
* ``test_unified_client_events_rts.py`` — error/remote events, format_dbc, RTS

Fixtures:

* ``simple_dbc`` — comes from ``conftest.py`` (shared with sibling files)
* ``demo_dbc`` — local, only used by ``TestAletheiaClientWithDemoDBC``
"""

import json
import subprocess
import sys
import textwrap
import threading
from pathlib import Path

import pytest

from aletheia import AletheiaClient, Signal
from aletheia.client._types import ProcessError
from aletheia.dbc_converter import dbc_to_json
from aletheia.protocols import DBCDefinition


@pytest.fixture(name="demo_dbc")
def _demo_dbc() -> DBCDefinition:
    """Load the demo vehicle DBC."""
    dbc_path = Path(__file__).parent.parent.parent / "examples" / "demo" / "vehicle.dbc"
    return dbc_to_json(str(dbc_path))


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
            result = client.extract_signals(
                can_id=256, dlc=8, data=bytearray([100, 0, 0, 0, 0, 0, 0, 0]),
            )
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
            updated = client.update_frame(
                can_id=256, dlc=8, frame=original, signals={"TestSignal": 200.0},
            )
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
            client.send_frame(
                timestamp=1000, can_id=256, dlc=8,
                data=bytearray([50, 0, 0, 0, 0, 0, 0, 0]),
            )

            # Extract signals while streaming (should work!)
            result = client.extract_signals(
                can_id=256, dlc=8, data=bytearray([100, 0, 0, 0, 0, 0, 0, 0]),
            )
            assert result.get("TestSignal") == 100.0

            # Continue streaming
            client.send_frame(
                timestamp=2000, can_id=256, dlc=8,
                data=bytearray([60, 0, 0, 0, 0, 0, 0, 0]),
            )

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
            updated = client.update_frame(
                can_id=256, dlc=8, frame=original, signals={"TestSignal": 75.0},
            )

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
        with AletheiaClient() as client:
            response = client.parse_dbc(simple_dbc)
            assert response.get("status") == "success"

            client.close()
            client.close()  # Second close must be safe.
        # __exit__ calls close() a third time — also must be safe.

    def test_use_after_close_raises(self, simple_dbc: DBCDefinition) -> None:
        """Operations on a closed client must raise, not crash.

        After ``close()`` both ``_lib`` and ``_state`` are ``None``.
        ``_send_command`` must detect the uninitialized state and raise
        ``ProcessError``; any other behavior (crash, silent no-op, use of
        a dangling state pointer) would be a serious safety bug.
        Mirrors Go's ``TestUseAfterClose``.
        """
        with AletheiaClient() as client:
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
        * **Thread B** — ``TestSignal < 500`` → expected ``holds`` (200 < 500)
        * **Thread C** — ``TestSignal < 1000`` → expected ``complete`` (clean)

        The threads synchronise through a ``threading.Barrier`` so they're
        all inside the streaming loop simultaneously, which forces the FFI
        layer to juggle three concurrent state pointers. If any thread
        leaks state into another (shared global, stale cache, unprotected
        mutation), the verdicts will be wrong.
        """
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
            client.send_frame(
                timestamp=0, can_id=256, dlc=8,
                data=bytearray([1, 0, 0, 0, 0, 0, 0, 0]),
            )
            client.end_stream()

            # Second stream (same client, same DBC)
            client.start_stream()
            resp = client.send_frame(
                timestamp=1, can_id=256, dlc=8,
                data=bytearray([2, 0, 0, 0, 0, 0, 0, 0]),
            )
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
            capture_output=True, text=True, timeout=15, check=False,
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
