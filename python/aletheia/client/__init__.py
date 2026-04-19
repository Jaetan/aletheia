"""Aletheia Client sub-package — public API.

Names exported here are part of the stable public surface alongside the
top-level ``aletheia`` package. Both import paths
(``from aletheia import X`` and ``from aletheia.client import X``) are
supported; the top-level form is preferred in user code, and the
``aletheia.client`` form is kept for backward-compat and for consumers
that want the narrower namespace. Modules prefixed with ``_``
(``_client``, ``_ffi``, ``_helpers``, ``_types``, etc.) are private
implementation detail and may break between review rounds.

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
from ._ffi import RTSState
from ._types import (
    AletheiaError,
    BatchError,
    CANFrameTuple,
    FrameResponse,
    ProcessError,
    PropertyDiagnostic,
    ProtocolError,
    SignalExtractionResult,
    bytes_to_dlc,
    dlc_to_bytes,
)

# Public symbols — every name here is covered by basedpyright at ``strict``
# level. User-facing API is ``AletheiaClient``, the exception hierarchy, the
# response TypedDicts, and the byte/DLC converters.
__all__ = [
    "AletheiaClient", "AletheiaError", "BatchError", "bytes_to_dlc",
    "CANFrameTuple", "dlc_to_bytes", "FrameResponse",
    "ProcessError", "PropertyDiagnostic", "ProtocolError",
    "RTSState", "SignalExtractionResult",
]
