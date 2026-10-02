# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
"""Core tests for the unified AletheiaClient.

Covers basic operations, streaming, mixed signal/streaming flows, the
client lifecycle (close, restart, isolation), and state-machine error
paths.  Sibling files split out:

* ``test_unified_client_canfd_mux.py`` — CAN-FD frames and nested mux
* ``test_unified_client_events_rts.py`` — error/remote events, format_dbc, RTS

Fixtures:

* ``simple_dbc`` — comes from ``conftest.py`` (shared with sibling files)
* ``demo_dbc`` — local, only used by ``TestAletheiaClientWithDemoDBC``
"""

import contextlib
import json
import subprocess
import sys
import textwrap
from pathlib import Path

import pytest
from _stream_helpers import send_test_frame

from aletheia import (
    AletheiaClient,
    DBCDefinition,
    ProtocolError,
    Signal,
    StateError,
    ValidationError,
)
from aletheia.dbc import dbc_to_json
from aletheia.types import DLCCode


@pytest.fixture(name="demo_dbc")
def demo_dbc_fixture() -> DBCDefinition:
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
                can_id=256,
                dlc=DLCCode(8),
                data=bytearray([100, 0, 0, 0, 0, 0, 0, 0]),
            )
            assert result.get("TestSignal") == 100.0

    def test_build_frame(self, simple_dbc: DBCDefinition) -> None:
        """Test frame building."""
        with AletheiaClient() as client:
            client.parse_dbc(simple_dbc)
            frame = client.build_frame(can_id=256, dlc=DLCCode(8), signals={"TestSignal": 1000})
            assert len(frame) == 8
            # Verify by extracting
            result = client.extract_signals(can_id=256, dlc=DLCCode(8), data=frame)
            assert result.get("TestSignal") == 1000.0

    def test_update_frame(self, simple_dbc: DBCDefinition) -> None:
        """Test frame updating."""
        with AletheiaClient() as client:
            client.parse_dbc(simple_dbc)
            original = bytearray([50, 0, 0, 0, 0, 0, 0, 0])
            updated = client.update_frame(
                can_id=256,
                dlc=DLCCode(8),
                frame=original,
                signals={"TestSignal": 200},
            )
            assert len(updated) == 8
            # Verify
            result = client.extract_signals(can_id=256, dlc=DLCCode(8), data=updated)
            assert result.get("TestSignal") == 200.0


class TestAletheiaClientStreaming:
    """Streaming LTL tests."""

    def test_streaming_no_violation(self, simple_dbc: DBCDefinition) -> None:
        """Test streaming without violations."""
        with AletheiaClient() as client:
            client.parse_dbc(simple_dbc)
            client.set_properties([Signal("TestSignal").less_than(1000).always().to_dict()])
            client.start_stream()

            # Send frames that don't violate
            for i in range(10):
                response = client.send_frame(
                    timestamp=i * 1000,
                    can_id=256,
                    dlc=DLCCode(8),
                    data=bytearray([i * 10, 0, 0, 0, 0, 0, 0, 0]),  # Values 0-90
                )
                assert response.get("status") == "ack"

            response = client.end_stream()
            assert response.get("status") == "complete"

    def test_streaming_with_violation(self, simple_dbc: DBCDefinition) -> None:
        """Test streaming with a violation."""
        with AletheiaClient() as client:
            client.parse_dbc(simple_dbc)
            client.set_properties([Signal("TestSignal").less_than(100).always().to_dict()])
            client.start_stream()

            # Send frame that violates (value = 200 > 100)
            response = send_test_frame(client, [200, 0, 0, 0, 0, 0, 0, 0])
            # send_frame returns a PropertyBatchResponse; the violation is the
            # (typically single) entry in results.
            assert "type" in response
            assert any(e["status"] == "fails" for e in response["results"])

            client.end_stream()

    def test_send_frame_over_ceiling_timestamp_rejected(self, simple_dbc: DBCDefinition) -> None:
        """A timestamp beyond the unsigned 64-bit wire field is refused up front.

        Regression: the binary FFI's timestamp slot is unsigned 64-bit, and
        the ctypes boundary masks an over-range Python int modulo the slot
        width.  Before the bound, sending ``2**64 + 1000`` µs after an
        accepted frame at 5000 µs — strictly larger, so an honest crossing
        is monotonic — reached the kernel as 1000 µs and came back as a
        ``handler_non_monotonic_timestamp`` error naming the wrapped value.
        """
        with AletheiaClient() as client:
            client.parse_dbc(simple_dbc)
            client.set_properties([])
            client.start_stream()
            response = client.send_frame(
                timestamp=5000,
                can_id=256,
                dlc=DLCCode(8),
                data=bytearray(8),
            )
            assert response.get("status") == "ack"
            with pytest.raises(ValidationError, match="unsigned 64-bit"):
                client.send_frame(
                    timestamp=2**64 + 1000,
                    can_id=256,
                    dlc=DLCCode(8),
                    data=bytearray(8),
                )
            client.end_stream()


class TestAletheiaClientMixedOperations:
    """Test mixing signal operations with streaming."""

    def test_extract_while_streaming(self, simple_dbc: DBCDefinition) -> None:
        """Test that extract_signals works while streaming."""
        with AletheiaClient() as client:
            client.parse_dbc(simple_dbc)
            client.set_properties([Signal("TestSignal").less_than(1000).always().to_dict()])
            client.start_stream()

            # Send a frame
            send_test_frame(client, [50, 0, 0, 0, 0, 0, 0, 0])

            # Extract signals while streaming (should work!)
            result = client.extract_signals(
                can_id=256,
                dlc=DLCCode(8),
                data=bytearray([100, 0, 0, 0, 0, 0, 0, 0]),
            )
            assert result.get("TestSignal") == 100.0

            # Continue streaming
            client.send_frame(
                timestamp=2000,
                can_id=256,
                dlc=DLCCode(8),
                data=bytearray([60, 0, 0, 0, 0, 0, 0, 0]),
            )

            client.end_stream()

    def test_update_while_streaming(self, simple_dbc: DBCDefinition) -> None:
        """Test that update_frame works while streaming."""
        with AletheiaClient() as client:
            client.parse_dbc(simple_dbc)
            client.set_properties([Signal("TestSignal").less_than(1000).always().to_dict()])
            client.start_stream()

            # Update a frame while streaming
            original = bytearray([50, 0, 0, 0, 0, 0, 0, 0])
            updated = client.update_frame(
                can_id=256,
                dlc=DLCCode(8),
                frame=original,
                signals={"TestSignal": 75},
            )

            # Send the updated frame
            response = client.send_frame(timestamp=1000, can_id=256, dlc=DLCCode(8), data=updated)
            assert response.get("status") == "ack"

            client.end_stream()

    def test_build_while_streaming(self, simple_dbc: DBCDefinition) -> None:
        """Test that build_frame works while streaming."""
        with AletheiaClient() as client:
            client.parse_dbc(simple_dbc)
            client.set_properties([Signal("TestSignal").less_than(1000).always().to_dict()])
            client.start_stream()

            # Build a frame while streaming
            frame = client.build_frame(can_id=256, dlc=DLCCode(8), signals={"TestSignal": 500})

            # Send it
            response = client.send_frame(timestamp=1000, can_id=256, dlc=DLCCode(8), data=frame)
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
        ``StateError``; any other behavior (crash, silent no-op, use of
        a dangling state pointer) would be a serious safety bug.
        Mirrors Go's ``TestUseAfterClose``.
        """
        with AletheiaClient() as client:
            client.parse_dbc(simple_dbc)
            client.close()

            with pytest.raises(StateError, match="not initialized"):
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
        with pytest.raises(StateError, match="not initialized"):
            client.parse_dbc(simple_dbc)

        # Double-close on the already-closed client must also be safe.
        client.close()

    def test_in_process_interleaved_clients(self, simple_dbc: DBCDefinition) -> None:
        """Three clients in the pytest process keep their streams apart, call by call.

        Each client holds kernel state of its own.  The three stream the same
        frame payload (``TestSignal = 200``) against different thresholds, and
        their calls are interleaved frame by frame, A then B then C, so every
        call of one lands between calls of the others: a client that leaked state
        into another (a shared global, a stale cache, an unprotected mutation)
        would give a wrong verdict.  The interleaving is driven, the same order
        on every run; ``test_isolated_clients_under_two_capabilities`` repeats it
        under an RTS of two capabilities.

        * **A**: ``TestSignal < 100`` fails on the first frame (200 is not < 100)
        * **B**: ``TestSignal < 500`` completes clean
        * **C**: ``TestSignal < 1000`` completes clean
        """
        thresholds = {"A": 100, "B": 500, "C": 1000}
        frames = [
            (i * 1000, 256, DLCCode(8), bytearray([200, 0, 0, 0, 0, 0, 0, 0])) for i in range(10)
        ]
        results: dict[str, str | None] = dict.fromkeys(thresholds)
        with contextlib.ExitStack() as stack:
            clients = {name: stack.enter_context(AletheiaClient()) for name in thresholds}
            for name, client in clients.items():
                client.parse_dbc(simple_dbc)
                client.set_properties(
                    [Signal("TestSignal").less_than(thresholds[name]).always().to_dict()]
                )
                client.start_stream()
            for ts, cid, dlc, data in frames:
                for name, client in clients.items():
                    if results[name] is not None:
                        continue
                    resp = client.send_frame(timestamp=ts, can_id=cid, dlc=dlc, data=data)
                    if "type" in resp and any(e.get("status") == "fails" for e in resp["results"]):
                        results[name] = "fails"
                        client.end_stream()
            for name, client in clients.items():
                if results[name] is None:
                    results[name] = client.end_stream().get("status")
        assert results == {"A": "fails", "B": "complete", "C": "complete"}

    def test_restart_stream(self, simple_dbc: DBCDefinition) -> None:
        """Stream can be restarted after end_stream."""
        with AletheiaClient() as client:
            client.parse_dbc(simple_dbc)
            client.set_properties([Signal("TestSignal").less_than(65535).always().to_dict()])

            # First stream
            client.start_stream()
            client.send_frame(
                timestamp=0,
                can_id=256,
                dlc=DLCCode(8),
                data=bytearray([1, 0, 0, 0, 0, 0, 0, 0]),
            )
            client.end_stream()

            # Second stream (same client, same DBC)
            client.start_stream()
            resp = client.send_frame(
                timestamp=1,
                can_id=256,
                dlc=DLCCode(8),
                data=bytearray([2, 0, 0, 0, 0, 0, 0, 0]),
            )
            assert resp.get("status") == "ack"
            client.end_stream()

    def test_isolated_clients_under_two_capabilities(self) -> None:
        """Two clients keep their streams apart under an RTS of two capabilities.

        Runs in a subprocess so the GHC RTS is initialised fresh with ``-N2``
        (two capabilities).  Both clients send the same frames (TestSignal =
        200) against different thresholds, their calls interleaved frame by
        frame in a driven order: A expects a violation (< 100), B none (< 1000).
        """
        script = textwrap.dedent("""\
            import contextlib, json
            from aletheia import AletheiaClient, Signal

            DBC = {
                "version": "1.0",
                "messages": [{
                    "id": 256, "name": "TestMessage", "dlc": 8,
                    "sender": "ECU",
                    "signals": [{
                        "name": "TestSignal", "startBit": 0, "length": 16,
                        "byteOrder": "little_endian", "signed": False,
                        "factor": 1, "offset": 0,
                        "minimum": 0, "maximum": 65535,
                        "unit": "", "presence": "always"
                    }]
                }]
            }
            FRAMES = [
                (i * 1000, 256, 8, bytearray([200, 0, 0, 0, 0, 0, 0, 0]))
                for i in range(20)
            ]
            THRESHOLDS = {"A": 100, "B": 1000}
            results = {}
            with contextlib.ExitStack() as stack:
                clients = {
                    name: stack.enter_context(AletheiaClient(rts_cores=2)) for name in THRESHOLDS
                }
                for name, client in clients.items():
                    client.parse_dbc(DBC)
                    client.set_properties([
                        Signal("TestSignal").less_than(THRESHOLDS[name]).always().to_dict()
                    ])
                    client.start_stream()
                for ts, cid, dlc, data in FRAMES:
                    for name, client in clients.items():
                        if name in results:
                            continue
                        resp = client.send_frame(timestamp=ts, can_id=cid, dlc=dlc, data=data)
                        if resp.get("type") == "property_batch" and any(
                            e.get("status") == "fails" for e in resp["results"]
                        ):
                            results[name] = "fails"
                            client.end_stream()
                for name, client in clients.items():
                    if name not in results:
                        results[name] = client.end_stream().get("status")
            print(json.dumps(results))
        """)
        result = subprocess.run(
            [sys.executable, "-c", script],
            capture_output=True,
            text=True,
            check=False,
        )
        assert result.returncode == 0, (
            f"Subprocess failed:\nstdout: {result.stdout}\nstderr: {result.stderr}"
        )
        assert json.loads(result.stdout) == {"A": "fails", "B": "complete"}


class TestAletheiaClientWithDemoDBC:
    """Tests using the demo vehicle DBC."""

    def test_vehicle_speed_extraction(self, demo_dbc: DBCDefinition) -> None:
        """Test extracting vehicle speed from demo DBC."""
        with AletheiaClient() as client:
            client.parse_dbc(demo_dbc)

            # Build a frame with speed = 72 kph
            frame = client.build_frame(can_id=0x100, dlc=DLCCode(8), signals={"VehicleSpeed": 72})

            # Extract and verify
            result = client.extract_signals(can_id=0x100, dlc=DLCCode(8), data=frame)
            assert abs(result.get("VehicleSpeed") - 72.0) < 0.01

    def test_fault_injection_single_session(self, demo_dbc: DBCDefinition) -> None:
        """Test fault injection in a single streaming session."""
        with AletheiaClient() as client:
            client.parse_dbc(demo_dbc)
            client.set_properties([Signal("VehicleSpeed").less_than(120).always().to_dict()])
            client.start_stream()

            # Send normal frames
            for i in range(5):
                frame = client.build_frame(
                    can_id=0x100,
                    dlc=DLCCode(8),
                    signals={"VehicleSpeed": 50 + i},
                )
                response = client.send_frame(
                    timestamp=i * 100000,
                    can_id=0x100,
                    dlc=DLCCode(8),
                    data=frame,
                )
                assert response.get("status") == "ack"

            # Inject fault: speed = 130 kph (exceeds 120 limit)
            fault_frame = client.build_frame(
                can_id=0x100,
                dlc=DLCCode(8),
                signals={"VehicleSpeed": 130},
            )
            response = client.send_frame(
                timestamp=500000,
                can_id=0x100,
                dlc=DLCCode(8),
                data=fault_frame,
            )
            # PropertyBatchResponse with a violation entry.
            assert "type" in response
            assert any(e.get("status") == "fails" for e in response["results"])

            client.end_stream()


class TestStateMachineErrors:
    """Test that invalid state transitions produce correct errors."""

    def test_extract_signals_without_dbc(self) -> None:
        """extract_signals before parse_dbc — Agda kernel rejects (ProtocolError).

        Unlike build_frame / update_frame (which check the populated
        signal-lookup cache client-side and raise StateError), the
        ``extract_signals`` JSON path is the rule the kernel enforces:
        no signal_lookup is populated until ``parse_dbc`` succeeds, so
        the request reaches the FFI and the Agda kernel returns
        ``handler_no_dbc``, which the binding lifts to ``ProtocolError``
        carrying the wire code.
        """
        with AletheiaClient() as client, pytest.raises(ProtocolError, match="DBC not loaded"):
            client.extract_signals(can_id=256, dlc=DLCCode(8), data=bytearray(8))

    def test_build_frame_without_dbc(self) -> None:
        """build_frame before parse_dbc raises StateError client-side."""
        with AletheiaClient() as client, pytest.raises(StateError, match="DBC not loaded"):
            client.build_frame(can_id=256, dlc=DLCCode(8), signals={"Sig": 1})

    def test_send_frame_without_stream(self, simple_dbc: DBCDefinition) -> None:
        """send_frame before start_stream returns error response."""
        with AletheiaClient() as client:
            client.parse_dbc(simple_dbc)
            client.set_properties([Signal("TestSignal").less_than(1000).always().to_dict()])
            response = client.send_frame(
                timestamp=0,
                can_id=256,
                dlc=DLCCode(8),
                data=bytearray(8),
            )
            assert response.get("status") == "error"

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
            client.set_properties(
                [
                    # Predicate targets a signal that is not in simple_dbc —
                    # therefore never evaluated on any frame, so its verdict stays
                    # Unknown at end-of-stream.
                    Signal("UnknownSignal").less_than(100).always().to_dict()
                ]
            )
            client.start_stream()
            # Send an unrelated frame that carries TestSignal only.
            send_test_frame(client, [10, 0, 0, 0, 0, 0, 0, 0])
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
            client.set_properties([Signal("TestSignal").less_than(1000).always().to_dict()])
            client.start_stream()

            # First frame at t=5000 µs — accepted.
            ok = client.send_frame(
                timestamp=5000,
                can_id=256,
                dlc=DLCCode(8),
                data=bytearray([10, 0, 0, 0, 0, 0, 0, 0]),
            )
            assert ok.get("status") == "ack"

            # Regressing to t=4999 µs — rejected.
            err = client.send_frame(
                timestamp=4999,
                can_id=256,
                dlc=DLCCode(8),
                data=bytearray([11, 0, 0, 0, 0, 0, 0, 0]),
            )
            assert "code" in err  # narrows to ErrorResponse
            assert err["status"] == "error"
            assert err["code"] == "handler_non_monotonic_timestamp"

            # Same-timestamp frames (≥, not >) are accepted.
            eq = client.send_frame(
                timestamp=5000,
                can_id=256,
                dlc=DLCCode(8),
                data=bytearray([12, 0, 0, 0, 0, 0, 0, 0]),
            )
            assert eq.get("status") == "ack"

            # Anchor is unchanged after rejection — next ≥ 5000 still accepted.
            fwd = client.send_frame(
                timestamp=6000,
                can_id=256,
                dlc=DLCCode(8),
                data=bytearray([13, 0, 0, 0, 0, 0, 0, 0]),
            )
            assert fwd.get("status") == "ack"

            client.end_stream()
