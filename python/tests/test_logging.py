"""Tests for opt-in structured logging.

Verifies that the 15 log events shared with Go's ``slog`` and the C++
``Logger`` class are emitted at the correct levels with the expected
fields.  Uses Python's standard ``logging`` module with a capturing
handler — no output is produced unless a handler is installed, matching
the opt-in design.
"""

import logging

import pytest

from aletheia import AletheiaClient, Signal
from aletheia.client._log import KNOWN_EVENTS, LogEvent
from aletheia.protocols import DBCDefinition


class _Capture(logging.Handler):
    """Logging handler that collects records into a list."""

    def __init__(self) -> None:
        super().__init__()
        self.records: list[logging.LogRecord] = []

    def emit(self, record: logging.LogRecord) -> None:
        self.records.append(record)


@pytest.fixture(name="capture")
def _capture() -> _Capture:
    """Install a capturing handler on the ``aletheia`` logger."""
    logger = logging.getLogger("aletheia")
    handler = _Capture()
    handler.setLevel(logging.DEBUG)
    logger.addHandler(handler)
    original_level = logger.level
    logger.setLevel(logging.DEBUG)
    yield handler
    logger.removeHandler(handler)
    logger.setLevel(original_level)


class TestLoggingStreamingEvents:
    """Verify that streaming workflow emits the expected log events."""

    def test_no_logging_without_handler(self, simple_dbc: DBCDefinition) -> None:
        """Without a handler installed, nothing crashes."""
        with AletheiaClient() as client:
            client.parse_dbc(simple_dbc)
            client.set_properties([
                Signal("TestSignal").less_than(1000).always().to_dict(),
            ])
            client.start_stream()
            client.send_frame(
                timestamp=1000, can_id=256, dlc=8,
                data=bytearray(8),
            )
            client.end_stream()

    def test_streaming_ack_events(
        self, simple_dbc: DBCDefinition, capture: _Capture,
    ) -> None:
        """properties.set, stream.started, frame.processed(ack), stream.ended."""
        with AletheiaClient() as client:
            client.parse_dbc(simple_dbc)
            client.set_properties([
                Signal("TestSignal").less_than(1000).always().to_dict(),
            ])
            client.start_stream()
            client.send_frame(
                timestamp=1000, can_id=256, dlc=8,
                data=bytearray([10, 0, 0, 0, 0, 0, 0, 0]),
            )
            client.end_stream()

        messages = [r.getMessage() for r in capture.records]

        # properties.set
        props_msgs = [m for m in messages if m.startswith("properties.set")]
        assert len(props_msgs) == 1
        assert "count=1" in props_msgs[0]

        # stream.started
        assert any(m == "stream.started" for m in messages)

        # frame.processed ... response=ack
        frame_msgs = [m for m in messages if m.startswith("frame.processed")]
        assert len(frame_msgs) >= 1
        assert "response=ack" in frame_msgs[0]
        assert "canId=256" in frame_msgs[0]

        # stream.ended
        ended_msgs = [m for m in messages if m.startswith("stream.ended")]
        assert len(ended_msgs) == 1
        assert "numResults=1" in ended_msgs[0]
        assert "numFails=0" in ended_msgs[0]

    def test_streaming_violation_events(
        self, simple_dbc: DBCDefinition, capture: _Capture,
    ) -> None:
        """Violation path logs frame.processed with response=violation."""
        with AletheiaClient() as client:
            client.parse_dbc(simple_dbc)
            client.set_properties([
                Signal("TestSignal").less_than(100).always().to_dict(),
            ])
            client.start_stream()
            # Value 200 > 100 → violation
            client.send_frame(
                timestamp=1000, can_id=256, dlc=8,
                data=bytearray([200, 0, 0, 0, 0, 0, 0, 0]),
            )
            client.end_stream()

        messages = [r.getMessage() for r in capture.records]

        # frame.processed with violation
        frame_msgs = [m for m in messages if m.startswith("frame.processed")]
        assert any("response=violation" in m for m in frame_msgs)

        # cache.miss (first extraction for enrichment)
        assert any(m.startswith("cache.miss") for m in messages)

    def test_stream_ended_counts_fails(
        self, simple_dbc: DBCDefinition, capture: _Capture,
    ) -> None:
        """stream.ended includes correct numFails count.

        The Always property violation is reported inline during send_frame,
        so end-of-stream finalization reports numFails=0 (already resolved).
        """
        with AletheiaClient() as client:
            client.parse_dbc(simple_dbc)
            client.set_properties([
                Signal("TestSignal").less_than(100).always().to_dict(),
            ])
            client.start_stream()
            # Value 200 > 100 triggers mid-stream violation
            client.send_frame(
                timestamp=1000, can_id=256, dlc=8,
                data=bytearray([200, 0, 0, 0, 0, 0, 0, 0]),
            )
            client.end_stream()

        messages = [r.getMessage() for r in capture.records]

        # Violation reported inline
        frame_msgs = [m for m in messages if m.startswith("frame.processed")]
        assert any("response=violation" in m for m in frame_msgs)

        # End-of-stream: property already failed inline → numFails=0
        ended_msgs = [m for m in messages if m.startswith("stream.ended")]
        assert len(ended_msgs) == 1
        assert "numResults=1" in ended_msgs[0]
        assert "numFails=0" in ended_msgs[0]

    def test_log_levels(
        self, simple_dbc: DBCDefinition, capture: _Capture,
    ) -> None:
        """Verify correct log levels for each event type."""
        with AletheiaClient() as client:
            client.parse_dbc(simple_dbc)
            client.set_properties([
                Signal("TestSignal").less_than(1000).always().to_dict(),
            ])
            client.start_stream()
            client.send_frame(
                timestamp=1000, can_id=256, dlc=8,
                data=bytearray([10, 0, 0, 0, 0, 0, 0, 0]),
            )
            client.end_stream()

        for record in capture.records:
            msg = record.getMessage()
            if msg.startswith(("properties.set", "stream.started", "stream.ended")):
                assert record.levelno == logging.INFO, (
                    f"Expected INFO for {msg}, got {record.levelname}"
                )
            elif msg.startswith(("frame.processed", "cache.hit", "cache.miss")):
                assert record.levelno == logging.DEBUG, (
                    f"Expected DEBUG for {msg}, got {record.levelname}"
                )
            elif msg.startswith(("cache.full", "enrichment.")):
                assert record.levelno == logging.WARNING, (
                    f"Expected WARNING for {msg}, got {record.levelname}"
                )


class TestLoggingSchema:
    """Guard the structured log-event vocabulary against accidental drift.

    Every log record emitted by the client must carry a ``LogRecord.event``
    attribute whose value is a member of :class:`LogEvent` — matching the
    Go ``slog`` and C++ ``Logger`` event sets documented in CLAUDE.md.
    """

    def test_known_events_matches_enum(self) -> None:
        """``KNOWN_EVENTS`` is derived from ``LogEvent`` and has 15 names."""
        assert KNOWN_EVENTS == {event.value for event in LogEvent}
        assert len(KNOWN_EVENTS) == 15

    def test_event_names_follow_namespace_dot_action(self) -> None:
        """All events are of the form ``namespace.action`` for grep-ability."""
        for name in KNOWN_EVENTS:
            assert "." in name, f"event {name!r} missing ``.`` separator"
            namespace, action = name.split(".", 1)
            assert namespace and action, f"event {name!r} has empty parts"

    def test_all_emitted_events_are_known(
        self, simple_dbc: DBCDefinition, capture: _Capture,
    ) -> None:
        """Every record from a streaming+violation workflow uses a known event."""
        with AletheiaClient() as client:
            client.parse_dbc(simple_dbc)
            client.set_properties([
                Signal("TestSignal").less_than(100).always().to_dict(),
            ])
            client.start_stream()
            # Violation path exercises enrichment + cache warmup.
            client.send_frame(
                timestamp=1000, can_id=256, dlc=8,
                data=bytearray([200, 0, 0, 0, 0, 0, 0, 0]),
            )
            client.end_stream()

        # Every record must carry ``extra["event"]`` — the structured key
        # that downstream JSON collectors pick up — AND that value must
        # be a member of the cross-binding vocabulary.
        assert capture.records, "expected at least one log record"
        for record in capture.records:
            event = getattr(record, "event", None)
            assert event is not None, (
                f"record {record.getMessage()!r} missing ``event`` attr"
            )
            assert event in KNOWN_EVENTS, (
                f"record emitted unknown event {event!r}; "
                f"add it to LogEvent or switch the call site"
            )
