"""Aletheia - Formally verified CAN frame analysis with LTL

AletheiaClient
==============

AletheiaClient provides streaming LTL checking and signal operations:

    from aletheia import AletheiaClient, Signal

    with AletheiaClient() as client:
        client.parse_dbc(dbc_json)

        # Signal operations work anytime after DBC loaded
        result = client.extract_signals(can_id=0x100, dlc=8, data=frame_bytes)
        speed = result.get("VehicleSpeed", 0.0)

        # Build frames from signal values
        frame = client.build_frame(can_id=0x100, dlc=8, signals={"VehicleSpeed": 50.0})

        # Update specific signals in a frame
        modified = client.update_frame(
            can_id=0x100, dlc=8, frame=data,
            signals={"VehicleSpeed": 130.0},
        )

        # Streaming LTL checking
        client.set_properties([Signal("Speed").less_than(220).always().to_dict()])
        client.start_stream()

        for frame in can_trace:
            # Signal ops work while streaming too!
            response = client.send_frame(timestamp, can_id, dlc, data)

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

from importlib.metadata import PackageNotFoundError, version as _pkg_version

# pylint: disable=cyclic-import
# __init__.py re-exports from submodules; client.py lazily imports
# `from . import _install_config` which technically creates a cycle
# through this file. It is a deferred import with no runtime issue.
from .client import (
    AletheiaClient,
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
from .checks import Check, CheckResult
from .dsl import Signal, Predicate, Property, infinitely_often, eventually_always, never
from .dbc_queries import (
    is_multiplexed,
    always_present_signals,
    multiplexed_signals,
    multiplexor_names,
    mux_values,
    signals_for_mux_value,
    message_by_id,
    message_by_name,
    signal_by_name,
)

# Optional-dependency modules: available when the corresponding extras are
# installed (``pip install aletheia[dbc]``, ``[can]``, ``[yaml]``, ``[excel]``,
# or ``[all]``).  Missing optional packages produce ImportError at call time,
# not at import time, so the core client is always usable.
#
# Each try/except narrows to the specific optional dependency via
# ``ImportError.name`` so that unrelated import failures inside the optional
# module (e.g. a syntax error or a broken sibling import) still surface loudly
# instead of being silently swallowed.
def _missing_pkg(exc: ImportError, pkg: str) -> bool:
    return (exc.name or "").split(".", 1)[0] == pkg


try:
    from .dbc_converter import dbc_to_json, dbc_to_text
except ImportError as _e:
    if not _missing_pkg(_e, "cantools"):
        raise

try:
    from .can_log import load_can_log, iter_can_log
except ImportError as _e:
    if not _missing_pkg(_e, "can"):
        raise

try:
    from .yaml_loader import load_checks
except ImportError as _e:
    if not _missing_pkg(_e, "yaml"):
        raise

try:
    from .excel_loader import load_checks_from_excel, load_dbc_from_excel, create_template
except ImportError as _e:
    if not _missing_pkg(_e, "openpyxl"):
        raise

try:
    __version__ = _pkg_version("aletheia")
except PackageNotFoundError:
    __version__ = "0.0.0"  # Development mode — not installed via pip
__all__ = [
    # Client
    "AletheiaClient",
    "CANFrameTuple",
    "SignalExtractionResult",
    "bytes_to_dlc",
    "dlc_to_bytes",
    # Exceptions & response types
    "AletheiaError",
    "BatchError",
    "FrameResponse",
    "ProcessError",
    "ProtocolError",
    # Check API
    "Check",
    "CheckResult",
    # Excel loader (optional: pip install aletheia[excel])
    "load_checks_from_excel",
    "load_dbc_from_excel",
    "create_template",
    # CAN log reader (optional: pip install aletheia[can])
    "load_can_log",
    "iter_can_log",
    # DBC converter (optional: pip install aletheia[dbc])
    "dbc_to_json",
    "dbc_to_text",
    # YAML loader (optional: pip install aletheia[yaml])
    "load_checks",
    # DBC queries
    "is_multiplexed",
    "always_present_signals",
    "multiplexed_signals",
    "multiplexor_names",
    "mux_values",
    "signals_for_mux_value",
    "message_by_id",
    "message_by_name",
    "signal_by_name",
    # DSL
    "Signal",
    "Predicate",
    "Property",
    "infinitely_often",
    "eventually_always",
    "never",
]
