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

from aletheia.client._backend import Backend, BinaryPathUnsupportedError, FFIBackend, MockBackend
from aletheia.client._client import AletheiaClient
from aletheia.client._ffi import RTSState
from aletheia.client._types import (
    AletheiaError,
    BatchError,
    CANFrameTuple,
    FFIError,
    FrameResponse,
    FrameResult,
    InputBoundExceededError,
    PropertyDiagnostic,
    ProtocolError,
    SignalExtractionResult,
    StateError,
    ValidationError,
    bytes_to_dlc,
    check_dbc_text_size_bound,
    dlc_to_bytes,
)

# Public symbols — every name here is covered by basedpyright at ``strict``
# level. User-facing API is ``AletheiaClient``, the exception hierarchy, the
# response TypedDicts, and the byte/DLC converters.
#
# R0801 false positive: these names necessarily overlap a run in the top-level
# ``aletheia.__all__`` (which re-exports this client API). ``__all__`` must stay
# a sorted list literal for RUF022 and basedpyright re-export tracking, so the
# shared run cannot be factored out.
# pylint: disable=duplicate-code
__all__ = [
    "AletheiaClient",
    "AletheiaError",
    "Backend",
    "BatchError",
    "BinaryPathUnsupportedError",
    "CANFrameTuple",
    "FFIBackend",
    "FFIError",
    "FrameResponse",
    "FrameResult",
    "InputBoundExceededError",
    "MockBackend",
    "PropertyDiagnostic",
    "ProtocolError",
    "RTSState",
    "SignalExtractionResult",
    "StateError",
    "ValidationError",
    "bytes_to_dlc",
    "check_dbc_text_size_bound",
    "dlc_to_bytes",
]
# pylint: enable=duplicate-code
