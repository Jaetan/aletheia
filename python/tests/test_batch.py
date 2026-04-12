"""Tests for send_frames and BatchError."""

from unittest.mock import MagicMock, patch

import pytest

from aletheia.client._client import AletheiaClient
from aletheia.client._types import BatchError, ProcessError


def _make_client() -> AletheiaClient:
    """Create a client with a mocked library handle."""
    with patch.object(AletheiaClient, "__init__", lambda self, *a, **kw: None):
        client = AletheiaClient.__new__(AletheiaClient)
        return client


class TestSendFramesBatch:
    """Tests for the batch frame-sending method."""

    def test_all_succeed(self) -> None:
        client = _make_client()
        responses = [{"status": "ack"}, {"status": "ack"}, {"status": "ack"}]
        client.send_frame = MagicMock(side_effect=responses)

        frames = [
            (1000, 0x100, 8, bytearray(8), False),
            (2000, 0x100, 8, bytearray(8), False),
            (3000, 0x100, 8, bytearray(8), False),
        ]
        result = client.send_frames(frames)
        assert len(result) == 3
        assert all(r["status"] == "ack" for r in result)

    def test_mid_batch_exception_carries_partial_results(self) -> None:
        """A Python exception mid-batch stops and carries partial results."""
        client = _make_client()
        client.send_frame = MagicMock(
            side_effect=[{"status": "ack"}, ValueError("bad frame"), {"status": "ack"}]
        )

        frames = [
            (1000, 0x100, 8, bytearray(8), False),
            (2000, 0x100, 8, bytearray(8), False),
            (3000, 0x100, 8, bytearray(8), False),
        ]
        with pytest.raises(BatchError) as exc_info:
            client.send_frames(frames)

        err = exc_info.value
        assert len(err.partial_results) == 1
        assert err.partial_results[0]["status"] == "ack"
        assert isinstance(err.cause, ValueError)
        assert err.frame_index == 1

    def test_error_response_stops_batch(self) -> None:
        """An ErrorResponse mid-batch stops and raises BatchError."""
        client = _make_client()
        error_resp = {"status": "error", "code": "handler_non_monotonic_timestamp",
                      "message": "backward timestamp"}
        client.send_frame = MagicMock(
            side_effect=[{"status": "ack"}, error_resp, {"status": "ack"}]
        )

        frames = [
            (1000, 0x100, 8, bytearray(8), False),
            (2000, 0x100, 8, bytearray(8), False),
            (3000, 0x100, 8, bytearray(8), False),
        ]
        with pytest.raises(BatchError) as exc_info:
            client.send_frames(frames)

        err = exc_info.value
        # partial_results contains only successfully-processed frames;
        # the ErrorResponse is surfaced via err.cause + err.frame_index
        # (matches Go and C++ bindings).
        assert len(err.partial_results) == 1
        assert err.partial_results[0]["status"] == "ack"
        assert err.frame_index == 1
        assert isinstance(err.cause, ProcessError)
        assert "handler_non_monotonic_timestamp" in str(err.cause)
        # Third frame was never sent
        assert client.send_frame.call_count == 2

    def test_first_frame_error_empty_partial(self) -> None:
        client = _make_client()
        client.send_frame = MagicMock(side_effect=RuntimeError("fail"))

        frames = [(1000, 0x100, 8, bytearray(8), False)]
        with pytest.raises(BatchError) as exc_info:
            client.send_frames(frames)

        assert len(exc_info.value.partial_results) == 0
        assert exc_info.value.frame_index == 0

    def test_violation_does_not_stop_batch(self) -> None:
        client = _make_client()
        violation = {
            "status": "fails", "type": "property",
            "property_index": {"numerator": 0, "denominator": 1},
            "timestamp": {"numerator": 2000, "denominator": 1},
        }
        client.send_frame = MagicMock(
            side_effect=[{"status": "ack"}, violation, {"status": "ack"}]
        )

        frames = [
            (1000, 0x100, 8, bytearray(8), False),
            (2000, 0x100, 8, bytearray(8), False),
            (3000, 0x100, 8, bytearray(8), False),
        ]
        result = client.send_frames(frames)
        assert len(result) == 3
        assert result[0]["status"] == "ack"
        assert result[1]["status"] == "fails"
        assert result[2]["status"] == "ack"

    def test_cause_chaining(self) -> None:
        client = _make_client()
        client.send_frame = MagicMock(side_effect=RuntimeError("boom"))

        frames = [(1000, 0x100, 8, bytearray(8), False)]
        with pytest.raises(BatchError) as exc_info:
            client.send_frames(frames)

        err = exc_info.value
        assert err.__cause__ is err.cause
        assert isinstance(err.__cause__, RuntimeError)

    def test_str_contains_frame_index(self) -> None:
        client = _make_client()
        client.send_frame = MagicMock(side_effect=ValueError("bad data"))

        frames = [(1000, 0x100, 8, bytearray(8), False)]
        with pytest.raises(BatchError) as exc_info:
            client.send_frames(frames)

        assert "frame 0" in str(exc_info.value)
        assert "bad data" in str(exc_info.value)

    def test_empty_batch(self) -> None:
        client = _make_client()
        client.send_frame = MagicMock()

        result = client.send_frames([])
        assert result == []
        client.send_frame.assert_not_called()
