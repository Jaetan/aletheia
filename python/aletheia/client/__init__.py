"""Aletheia Client

Provides signal extraction, frame building, and streaming LTL checking
via a shared library (FFI) that calls the formally verified Agda core.

Example:
    from aletheia import AletheiaClient, Signal, dlc_to_bytes
    from aletheia.dbc_converter import dbc_to_json

    dbc = dbc_to_json("vehicle.dbc")

    with AletheiaClient() as client:
        client.parse_dbc(dbc)

        # Signal operations work anytime after DBC is loaded
        result = client.extract_signals(can_id=0x100, dlc=8, data=bytearray(8))
        speed = result.get("VehicleSpeed", 0.0)

        # Build a frame from signal values
        frame = client.build_frame(can_id=0x100, dlc=8, signals={"VehicleSpeed": 50.0})

        # Streaming LTL checking
        client.set_properties([Signal("VehicleSpeed").less_than(120).always().to_dict()])
        client.start_stream()

        for ts, can_id, dlc, data, ext in frames:
            # Can still use signal operations while streaming!
            modified = client.update_frame(can_id, dlc, data, {"VehicleSpeed": 130.0}, extended=ext)
            response = client.send_frame(ts, can_id, dlc, modified, extended=ext)

        client.end_stream()
"""

from ._client import AletheiaClient
# Re-exported for first-party consumers (``aletheia.cli``, ``dbc_converter``,
# ``excel_loader``). These are intentionally NOT documented in the user-facing
# API — ``AletheiaClient`` methods, DSL builders, and loader functions cover
# the supported surface. Kept in ``__all__`` purely so basedpyright at strict
# level recognises the re-export as deliberate; the `.client` path is fine
# for first-party imports but not part of the stable public contract.
from ._helpers import dump_json, to_signal_fraction
from ._types import (
    AletheiaError,
    BatchError,
    CANFrameTuple,
    FrameResponse,
    ProcessError,
    ProtocolError,
    SignalExtractionResult,
    bytes_to_dlc,
    dlc_to_bytes,
)

# Public symbols — every name here is covered by basedpyright at ``strict``
# level. User-facing API is ``AletheiaClient`` and the names below it; the
# ``dump_json``/``to_signal_fraction`` entries exist because first-party
# loader modules import them via the ``aletheia.client`` path and basedpyright
# otherwise flags them as unused. Treat them as package-internal.
__all__ = [
    "AletheiaClient", "AletheiaError", "BatchError", "bytes_to_dlc",
    "CANFrameTuple", "dlc_to_bytes", "dump_json", "FrameResponse",
    "ProcessError", "ProtocolError", "SignalExtractionResult",
    "to_signal_fraction",
]
