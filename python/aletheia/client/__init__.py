"""Aletheia Client

Provides signal extraction, frame building, and streaming LTL checking
via a shared library (FFI) that calls the formally verified Agda core.

Example:
    from aletheia import AletheiaClient, Signal
    from aletheia.dbc_converter import dbc_to_json

    dbc = dbc_to_json("vehicle.dbc")

    with AletheiaClient() as client:
        client.parse_dbc(dbc)

        # Signal operations work anytime after DBC is loaded
        result = client.extract_signals(can_id=0x100, data=bytearray(8))
        speed = result.get("VehicleSpeed", 0.0)

        # Build a frame from signal values
        frame = client.build_frame(can_id=0x100, signals={"VehicleSpeed": 50.0})

        # Streaming LTL checking
        client.set_properties([Signal("VehicleSpeed").less_than(120).always().to_dict()])
        client.start_stream()

        for ts, can_id, data in frames:
            # Can still use signal operations while streaming!
            modified = client.update_frame(can_id, data, {"VehicleSpeed": 130.0})
            response = client.send_frame(ts, can_id, modified)

        client.end_stream()
"""

from ._client import AletheiaClient
from ._types import (
    AletheiaError,
    ProcessError,
    ProtocolError,
    SignalExtractionResult,
)

__all__ = [
    "AletheiaClient",
    "AletheiaError",
    "ProcessError",
    "ProtocolError",
    "SignalExtractionResult",
]
