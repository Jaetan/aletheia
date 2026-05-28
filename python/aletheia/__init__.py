"""Aletheia - Formally verified CAN frame analysis with LTL.

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

from importlib.metadata import PackageNotFoundError
from importlib.metadata import version as _pkg_version

from aletheia.checks import CheckResult

# pylint: disable=cyclic-import
# __init__.py re-exports from submodules; ``client/_ffi.py`` lazily imports
# ``from .. import _install_config`` (an install-time-generated module) which
# technically creates a cycle through this file. The cycle is benign because
# the import is **deferred inside a function body** (see
# ``client/_ffi.py:find_ffi_library``), so this file finishes executing before
# the import is attempted.
#
# Boundary constraint: do NOT add a top-level ``from .client import ...`` name
# that is reached during ``_install_config`` resolution, and do NOT make
# ``_install_config`` import anything from ``aletheia`` or its submodules.
# Either change breaks the deferred-import contract and will turn this benign
# technical cycle into an ``ImportError`` at install-detection time.
# DEFERRED — TRACKED (R19P2-CL16-2 — DEFER).
# Finding: AletheiaError (canonical at aletheia/client/_types.py:18) is exposed
#   via two public paths: `from aletheia import AletheiaError` (re-exported
#   here) AND `from aletheia.client import AletheiaError` (re-exported by
#   client/__init__.py).  Documentation references the top-level form.
# Why DEFER: Deprecating `aletheia.client.AletheiaError` is mechanically safe
#   (re-export forwarder) but requires a deprecation warning + downstream user
#   code review.  Project has no current external users so the warning-period
#   is unnecessary, but the canonical-path decision is mostly cosmetic.
# Revisit when: First external user lands, OR a documentation sweep clarifies
#   the canonical import paths.
from aletheia.client import (
    AletheiaClient,
    AletheiaError,
    Backend,
    BatchError,
    BinaryPathUnsupportedError,
    CANFrameTuple,
    FFIBackend,
    FFIError,
    FrameResponse,
    FrameResult,
    InputBoundExceededError,
    MockBackend,
    PropertyDiagnostic,
    ProtocolError,
    RTSState,
    SignalExtractionResult,
    StateError,
    ValidationError,
    bytes_to_dlc,
    dlc_to_bytes,
)
from aletheia.dbc_converter import convert_dbc_file, dbc_to_json, dbc_to_text
from aletheia.dbc_queries import (
    always_present_signals,
    is_multiplexed,
    message_by_id,
    message_by_name,
    multiplexed_signals,
    multiplexor_names,
    mux_values,
    signal_by_name,
    signals_for_mux_value,
)
from aletheia.dsl import Predicate, Property, Signal, eventually_always, infinitely_often, never
from aletheia.error_codes import ErrorCode
from aletheia.issue_codes import IssueCode, ValidationIssue
from aletheia.protocols import (
    DBCDefinition,
    PropertyResultEntry,
)


# Optional-dependency modules: available when the corresponding extras are
# installed (``pip install aletheia[can]``, ``[yaml]``, ``[excel]``, or
# ``[all]``).  Missing optional packages produce ImportError at call time,
# not at import time, so the core client is always usable.
#
# Each try/except narrows to the specific optional dependency via
# ``ImportError.name`` so that unrelated import failures inside the optional
# module (e.g. a syntax error or a broken sibling import) still surface loudly
# instead of being silently swallowed.
def _missing_pkg(exc: ImportError, pkg: str) -> bool:
    return (exc.name or "").split(".", 1)[0] == pkg


try:
    from aletheia.can_log import iter_can_log, load_can_log
except ImportError as _e:
    if not _missing_pkg(_e, "can"):
        raise

try:
    from aletheia.yaml_loader import load_checks
except ImportError as _e:
    if not _missing_pkg(_e, "yaml"):
        raise

try:
    from aletheia.excel_loader import create_template, load_checks_from_excel, load_dbc_from_excel
except ImportError as _e:
    if not _missing_pkg(_e, "openpyxl"):
        raise

try:
    __version__ = _pkg_version("aletheia")
except PackageNotFoundError:
    __version__ = "0.0.0"  # Development mode — not installed via pip

# Static ``__all__`` covers the full public surface, including optional
# extras. Names backed by optional dependencies may not be importable if
# those packages aren't installed; ``from aletheia import *`` in that case
# raises ``AttributeError`` for the missing name, which is the documented
# behaviour for missing extras.
__all__ = [
    "AletheiaClient",
    "AletheiaError",
    "Backend",
    "BatchError",
    "BinaryPathUnsupportedError",
    "CANFrameTuple",
    "CheckResult",
    "DBCDefinition",
    "ErrorCode",
    "FFIBackend",
    "FFIError",
    "FrameResponse",
    "FrameResult",
    "InputBoundExceededError",
    "IssueCode",
    "MockBackend",
    "Predicate",
    "Property",
    "PropertyDiagnostic",
    "PropertyResultEntry",
    "ProtocolError",
    "RTSState",
    "Signal",
    "SignalExtractionResult",
    "StateError",
    "ValidationError",
    "ValidationIssue",
    "always_present_signals",
    "bytes_to_dlc",
    "convert_dbc_file",
    "create_template",  # pip install aletheia[excel]
    "dbc_to_json",
    "dbc_to_text",
    "dlc_to_bytes",
    "eventually_always",
    "infinitely_often",
    "is_multiplexed",
    "iter_can_log",  # pip install aletheia[can]
    "load_can_log",  # pip install aletheia[can]
    "load_checks",  # pip install aletheia[yaml]
    "load_checks_from_excel",  # pip install aletheia[excel]
    "load_dbc_from_excel",  # pip install aletheia[excel]
    "message_by_id",
    "message_by_name",
    "multiplexed_signals",
    "multiplexor_names",
    "mux_values",
    "never",
    "signal_by_name",
    "signals_for_mux_value",
]
