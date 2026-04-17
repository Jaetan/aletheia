"""Trace-event, format_dbc, and RTS-state tests for AletheiaClient.

Split out of ``test_unified_client.py`` to keep that file under the
1000-line pylint cap.  Covers three independent areas that share no
fixtures with the streaming/lifecycle tests:

* ``TestSendErrorRemote`` — ``send_error()`` / ``send_remote()`` response
  parsing, validation, and the ack path for trace events that bypass
  data-frame monotonicity.
* ``TestFormatDBC`` — ``format_dbc()`` round-trip.
* ``TestRTSState`` — GHC RTS reference counting and the
  ``rts.cores_mismatch`` warning.

The ``simple_dbc`` fixture comes from ``conftest.py``.
"""

import pytest

from aletheia import AletheiaClient, Signal
from aletheia.client._ffi import RTSState
from aletheia.client._response_parsers import parse_event_response
from aletheia.client._types import ProtocolError
from aletheia.protocols import DBCDefinition


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

    def test_send_error_success_status_rejected(self) -> None:
        """parse_event_response rejects "success" — trace events must emit "ack"."""
        with pytest.raises(ProtocolError, match="Unexpected error_event response status"):
            parse_event_response({"status": "success"}, "error_event", 1000)

    def test_send_remote_success_status_rejected(self) -> None:
        """parse_event_response rejects "success" — trace events must emit "ack"."""
        with pytest.raises(ProtocolError, match="Unexpected remote_event response status"):
            parse_event_response({"status": "success"}, "remote_event", 1000)

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
        initial = RTSState.refcount
        with AletheiaClient():
            assert RTSState.refcount == initial + 1
        assert RTSState.refcount == initial

    def test_release_does_not_go_negative(self) -> None:
        """release() when refcount is 0 stays at 0."""
        saved = RTSState.refcount
        RTSState.refcount = 0
        RTSState.release()
        assert RTSState.refcount == 0
        RTSState.refcount = saved

    def test_rts_cores_mismatch_warns(self, caplog: pytest.LogCaptureFixture) -> None:
        """Second client with different rts_cores logs a warning."""
        with AletheiaClient(rts_cores=1):
            with caplog.at_level("WARNING", logger="aletheia"):
                with AletheiaClient(rts_cores=4):
                    pass
            assert "rts.cores_mismatch" in caplog.text
