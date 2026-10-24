# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
"""Aletheia - Formally verified CAN frame analysis with LTL.

AletheiaClient
==============

AletheiaClient provides streaming LTL checking and signal operations:

```python
from aletheia import AletheiaClient, Signal
from aletheia.can_log import iter_can_log
from aletheia.dbc import dbc_to_json

with AletheiaClient() as client:
    client.parse_dbc(dbc_to_json("vehicle.dbc"))

    # Build frames from signal values
    frame = client.build_frame(can_id=0x100, dlc=8, signals={"VehicleSpeed": 50})

    # Signal operations work anytime after DBC loaded
    result = client.extract_signals(can_id=0x100, dlc=8, data=frame)
    speed = result.get("VehicleSpeed", 0)

    # Update specific signals in a frame
    modified = client.update_frame(
        can_id=0x100, dlc=8, frame=frame,
        signals={"VehicleSpeed": 130},
    )

    # Streaming LTL checking
    client.set_properties([Signal("VehicleSpeed").less_than(220).always().to_dict()])
    client.start_stream()

    for ts, can_id, dlc, data, ext, brs, esi in iter_can_log("drive.log"):
        # Signal ops work while streaming too!
        response = client.send_frame(ts, can_id, dlc, data, extended=ext, brs=brs, esi=esi)

    client.end_stream()
```

Python DSL for LTL Properties
==============================

Use the fluent Signal interface to build properties:

```python
# Temporal operators
Signal("Speed").less_than(220).always()
Signal("DoorClosed").equals(1).eventually()
Signal("ErrorCode").equals(0xFF).never()

# Composition
brake = Signal("Brake").equals(1)
throttle = Signal("Throttle")
speed_decreases = Signal("Speed").changed_by(-10)
brake.and_(throttle.equals(0))
brake.implies(speed_decreases.within(100)).always()
```
"""

import logging
from importlib.metadata import PackageNotFoundError
from importlib.metadata import version as _pkg_version

from aletheia import dbc
from aletheia.checks import CheckResult

# pylint: disable=cyclic-import
# The names below form the public surface but are *defined* inside the
# internal ``aletheia.client`` sub-package. ``aletheia`` is the single
# canonical public package — importing these names straight from
# ``aletheia.client`` is unsupported. We source them from the concrete
# ``_``-prefixed modules so importing ``aletheia`` does not eagerly pull the
# whole sub-package via ``client/__init__.py``.
#
# Cyclic-import note: ``client/_ffi.py`` lazily imports
# ``from .. import _install_config`` (an install-time-generated module), which
# technically creates a cycle through this file. The cycle is benign because
# the import is **deferred inside a function body** (see
# ``client/_ffi.py:find_ffi_library``), so this file finishes executing before
# the import is attempted. Boundary constraint: do NOT make ``_install_config``
# import anything from ``aletheia`` or its submodules, and do NOT add a
# top-level client import reached during ``_install_config`` resolution —
# either turns this benign technical cycle into an ``ImportError`` at
# install-detection time.
from aletheia.client._backend import (
    Backend,
    BinaryPathUnsupportedError,
    FFIBackend,
    MockBackend,
)
from aletheia.client._client import AletheiaClient
from aletheia.client._ffi import RTSState, allocated_bytes
from aletheia.client._helpers.rational import from_decimal
from aletheia.client._types import (
    AletheiaError,
    BatchError,
    CANFrameTuple,
    DBCValidationFailedError,
    FFIError,
    FrameResponse,
    FrameResult,
    InputBoundExceededError,
    PropertyDiagnostic,
    ProtocolError,
    SignalExtractionResult,
    StateError,
    TextRoundTripFailedError,
    ValidationError,
    bytes_to_dlc,
    dlc_to_bytes,
)
from aletheia.codes import ErrorCode, IssueCode, ValidationIssue

# The whole of ``aletheia.dbc``'s surface, named once in its own ``__all__``
# and added to this one below; ruff cannot see a star import's names.
from aletheia.dbc import *  # noqa: F403
from aletheia.dsl import Predicate, Property, Signal, eventually_always, infinitely_often, never
from aletheia.types import (
    DBCDefinition,
    PropertyResultEntry,
)

# The package prints nothing until the host configures the ``aletheia`` logger:
# the handler keeps logging's last-resort stderr handler out of the chain, as
# the C++, Go and Rust clients are silent until a logger is passed to them.
logging.getLogger("aletheia").addHandler(logging.NullHandler())


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
    "DBCValidationFailedError",
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
    "TextRoundTripFailedError",
    "ValidationError",
    "ValidationIssue",
    "allocated_bytes",
    "bytes_to_dlc",
    "create_template",  # pip install aletheia[excel]
    "dlc_to_bytes",
    "eventually_always",
    "from_decimal",
    "infinitely_often",
    "iter_can_log",  # pip install aletheia[can]
    "load_can_log",  # pip install aletheia[can]
    "load_checks",  # pip install aletheia[yaml]
    "load_checks_from_excel",  # pip install aletheia[excel]
    "load_dbc_from_excel",  # pip install aletheia[excel]
    "never",
]
# ``aletheia.dbc`` names its own public surface; every name in it is public here too.
__all__ += dbc.__all__
