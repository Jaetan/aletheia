# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
"""Tests for send_frames and BatchError."""

from unittest.mock import MagicMock

import pytest

from aletheia import AletheiaClient, BatchError, CANFrameTuple, ProtocolError
from aletheia.types import DLCCode


def _make_client() -> AletheiaClient:
    """Create a client with no FFI handle (``__new__`` bypasses ``__init__``)."""
    return AletheiaClient.__new__(AletheiaClient)


class TestSendFramesBatch:
    """Tests for the batch frame-sending method."""

    def test_all_succeed(self) -> None:
        """Verify all succeed."""
        client = _make_client()
        responses = [{"status": "ack"}, {"status": "ack"}, {"status": "ack"}]
        client.send_frame = MagicMock(side_effect=responses)

        frames = [
            CANFrameTuple(1000, 0x100, DLCCode(8), bytearray(8), extended=False),
            CANFrameTuple(2000, 0x100, DLCCode(8), bytearray(8), extended=False),
            CANFrameTuple(3000, 0x100, DLCCode(8), bytearray(8), extended=False),
        ]
        result = client.send_frames(frames)
        assert len(result) == 3
        # "status" in r narrows each entry to AckResponse before subscripting.
        assert all("status" in r and r["status"] == "ack" for r in result)

    def test_mid_batch_exception_carries_partial_results(self) -> None:
        """A Python exception mid-batch stops and carries partial results."""
        client = _make_client()
        client.send_frame = MagicMock(
            side_effect=[{"status": "ack"}, ValueError("bad frame"), {"status": "ack"}]
        )

        frames = [
            CANFrameTuple(1000, 0x100, DLCCode(8), bytearray(8), extended=False),
            CANFrameTuple(2000, 0x100, DLCCode(8), bytearray(8), extended=False),
            CANFrameTuple(3000, 0x100, DLCCode(8), bytearray(8), extended=False),
        ]
        with pytest.raises(BatchError) as exc_info:
            client.send_frames(frames)

        err = exc_info.value
        assert len(err.partial_results) == 1
        first = err.partial_results[0]
        assert "status" in first  # AckResponse
        assert first["status"] == "ack"
        assert isinstance(err.cause, ValueError)
        assert err.frame_index == 1

    def test_error_response_stops_batch(self) -> None:
        """An ErrorResponse mid-batch stops and raises BatchError."""
        client = _make_client()
        error_resp = {
            "status": "error",
            "code": "handler_non_monotonic_timestamp",
            "message": "backward timestamp",
        }
        client.send_frame = MagicMock(
            side_effect=[{"status": "ack"}, error_resp, {"status": "ack"}]
        )

        frames = [
            CANFrameTuple(1000, 0x100, DLCCode(8), bytearray(8), extended=False),
            CANFrameTuple(2000, 0x100, DLCCode(8), bytearray(8), extended=False),
            CANFrameTuple(3000, 0x100, DLCCode(8), bytearray(8), extended=False),
        ]
        with pytest.raises(BatchError) as exc_info:
            client.send_frames(frames)

        err = exc_info.value
        # partial_results contains only successfully-processed frames;
        # the ErrorResponse is surfaced via err.cause + err.frame_index
        # (matches Go and C++ bindings).
        assert len(err.partial_results) == 1
        first = err.partial_results[0]
        assert "status" in first  # AckResponse
        assert first["status"] == "ack"
        assert err.frame_index == 1
        assert isinstance(err.cause, ProtocolError)
        assert "handler_non_monotonic_timestamp" in str(err.cause)
        # Third frame was never sent
        assert client.send_frame.call_count == 2

    def test_first_frame_error_empty_partial(self) -> None:
        """Verify first frame error empty partial."""
        client = _make_client()
        client.send_frame = MagicMock(side_effect=RuntimeError("fail"))

        frames = [CANFrameTuple(1000, 0x100, DLCCode(8), bytearray(8), extended=False)]
        with pytest.raises(BatchError) as exc_info:
            client.send_frames(frames)

        assert len(exc_info.value.partial_results) == 0
        assert exc_info.value.frame_index == 0

    def test_violation_does_not_stop_batch(self) -> None:
        """Verify violation does not stop batch.

        Violation frames return a PropertyBatchResponse carrying one or
        more events; the batch continues regardless.
        """
        client = _make_client()
        violation_batch = {
            "type": "property_batch",
            "results": [
                {
                    "type": "property",
                    "status": "fails",
                    "property_index": {"numerator": 0, "denominator": 1},
                    "timestamp": {"numerator": 2000, "denominator": 1},
                }
            ],
        }
        client.send_frame = MagicMock(
            side_effect=[{"status": "ack"}, violation_batch, {"status": "ack"}]
        )

        frames = [
            CANFrameTuple(1000, 0x100, DLCCode(8), bytearray(8), extended=False),
            CANFrameTuple(2000, 0x100, DLCCode(8), bytearray(8), extended=False),
            CANFrameTuple(3000, 0x100, DLCCode(8), bytearray(8), extended=False),
        ]
        result = client.send_frames(frames)
        assert len(result) == 3
        first = result[0]
        second = result[1]
        third = result[2]
        assert "status" in first  # AckResponse
        assert first["status"] == "ack"
        assert "type" in second  # PropertyBatchResponse
        assert second["type"] == "property_batch"
        assert second["results"][0]["status"] == "fails"
        assert "status" in third  # AckResponse
        assert third["status"] == "ack"

    def test_cause_chaining(self) -> None:
        """Verify cause chaining."""
        client = _make_client()
        client.send_frame = MagicMock(side_effect=RuntimeError("boom"))

        frames = [CANFrameTuple(1000, 0x100, DLCCode(8), bytearray(8), extended=False)]
        with pytest.raises(BatchError) as exc_info:
            client.send_frames(frames)

        err = exc_info.value
        assert err.__cause__ is err.cause
        assert isinstance(err.__cause__, RuntimeError)

    def test_str_contains_frame_index(self) -> None:
        """Verify str contains frame index."""
        client = _make_client()
        client.send_frame = MagicMock(side_effect=ValueError("bad data"))

        frames = [CANFrameTuple(1000, 0x100, DLCCode(8), bytearray(8), extended=False)]
        with pytest.raises(BatchError) as exc_info:
            client.send_frames(frames)

        assert "frame 0" in str(exc_info.value)
        assert "bad data" in str(exc_info.value)

    def test_empty_batch(self) -> None:
        """Verify empty batch."""
        client = _make_client()
        client.send_frame = MagicMock()

        result = client.send_frames([])
        assert not result
        client.send_frame.assert_not_called()
