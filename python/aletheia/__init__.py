"""Aletheia - Formally verified CAN frame analysis with LTL

JSON Streaming Protocol (Phase 2B.1)
====================================

The primary interface is StreamingClient for incremental LTL checking:

    from aletheia import StreamingClient, Signal

    with StreamingClient() as client:
        client.parse_dbc(dbc_json)
        client.set_properties([
            Signal("Speed").less_than(220).always().to_dict()
        ])
        client.start_stream()

        for frame in can_trace:
            response = client.send_frame(timestamp, can_id, data)
            if response.get("type") == "property":
                print(f"Violation: {response}")

        client.end_stream()

Python DSL for LTL Properties
==============================

Use the fluent Signal interface to build properties:

    # Temporal operators
    Signal("Speed").less_than(220).always()
    Signal("DoorClosed").equals(1).eventually()
    Signal("ErrorCode").equals(0xFF).never()

    # Composition
    brake.and_(throttle.equals(0))
    brake.implies(speed_decreases.within(100))
"""

from aletheia.streaming_client import (
    StreamingClient,
    AletheiaError,
    ProcessError,
    ProtocolError,
)
from aletheia.dsl import Signal, Predicate, Property
from aletheia.signals import (
    FrameBuilder,
    SignalExtractor,
    SignalExtractionResult,
)

__version__ = "0.1.0"
__all__ = [
    "StreamingClient",
    "AletheiaError",
    "ProcessError",
    "ProtocolError",
    "Signal",
    "Predicate",
    "Property",
    "FrameBuilder",
    "SignalExtractor",
    "SignalExtractionResult",
]
