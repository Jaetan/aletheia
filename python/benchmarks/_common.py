"""Shared benchmark helpers: DBC loaders, frame constants, system info.

Every benchmark script in this directory pulls DBC loaders, frame byte
arrays, and ``get_system_info`` / ``get_rss_mb`` from this module so that a
drift (e.g. a signal layout change for the CAN-FD frame) only has to be
fixed in one place.  Keep the module-level constants ``bytes`` (not
``bytearray``) so a stray mutation between runs cannot silently skew the
numbers.

Per PY-31-1: this module is deliberately thin — each constant / function
has exactly one authoritative definition, and benchmark scripts import
what they need by name.  No re-export hoop, no star-imports; basedpyright
and pylint see a straight dependency.
"""

import os
import platform
import resource
from pathlib import Path

from aletheia.dbc_converter import dbc_to_json

# ``benchmarks/`` sits two levels below the repo root: python/benchmarks/X.py
# → ../../examples/.  Path is resolved once so re-importing this module
# is cheap; ``parents`` is immutable so no callers can mutate it.
_EXAMPLES_DIR = Path(__file__).resolve().parent.parent.parent / "examples"

# ============================================================================
# DBC loaders — single source for the demo databases used by every run.
# ============================================================================


def load_dbc() -> dict[str, object]:
    """Load the CAN 2.0B example DBC file."""
    return dbc_to_json(str(_EXAMPLES_DIR / "example.dbc"))


def load_canfd_dbc() -> dict[str, object]:
    """Load the CAN-FD example DBC file."""
    return dbc_to_json(str(_EXAMPLES_DIR / "example_canfd.dbc"))


# ============================================================================
# CAN 2.0B frame (DLC 8, 8 bytes).  Immutable ``bytes`` so an in-place
# rewrite during a benchmark cannot skew subsequent iterations.
# ============================================================================

CAN20_FRAME: bytes = bytes([0x40, 0x1F, 0x82, 0x00, 0x00, 0x00, 0x00, 0x00])
CAN20_CAN_ID: int = 0x100
CAN20_DLC: int = 8
CAN20_SIGNALS: dict[str, float] = {"EngineSpeed": 2000.0, "EngineTemp": 90.0}

# ============================================================================
# CAN-FD frame (DLC 15, 64 bytes) — sensor-fusion layout with realistic
# engineering values so the core's rational encoding path is exercised.
# ============================================================================

CANFD_FRAME: bytes = bytes(
    [0x00, 0xE1, 0xF5, 0x05]    # GPSLatitude  (raw ~100000000 → 10.0 deg)
    + [0x00, 0x6C, 0xDC, 0x02]  # GPSLongitude (raw ~48100000 → 4.81 deg)
    + [0xE8, 0x03]              # GPSAltitude  (raw 1000 → 100.0 m)
    + [0xD0, 0x07]              # GPSSpeed     (raw 2000 → 20.0 m/s)
    + [0x00, 0x00]              # YawRate      (raw 0 → 0.0 deg/s)
    + [0x00, 0x00]              # LateralAccel (raw 0)
    + [0x00, 0x00]              # LongAccel    (raw 0)
    + [0x00, 0x00]              # SteeringAngle(raw 0)
    + [0xE8, 0x03]              # WheelSpeedFL (raw 1000 → 10.0 m/s)
    + [0xE8, 0x03]              # WheelSpeedFR
    + [0xE8, 0x03]              # WheelSpeedRL
    + [0xE8, 0x03]              # WheelSpeedRR
    + [0x00] * 36               # Remaining signals + padding to 64 bytes
)
CANFD_CAN_ID: int = 0x200
CANFD_DLC: int = 15
CANFD_SIGNALS: dict[str, float] = {
    "GPSSpeed": 20.0,
    "YawRate": 0.0,
    "WheelSpeedFL": 10.0,
    "WheelSpeedFR": 10.0,
}


# ============================================================================
# System info & RSS — attached to every JSON report so results can be
# cross-referenced against the hardware they were measured on.
# ============================================================================


def get_system_info() -> dict[str, object]:
    """Collect system information for benchmark metadata.

    Returned dict is JSON-safe (strings and ints) so the caller can embed
    it directly in the benchmark's stdout payload.
    """
    return {
        "cpu": platform.processor() or platform.machine(),
        "cores": os.cpu_count() or 0,
        "platform": platform.system(),
        "python": platform.python_version(),
    }


def get_rss_mb() -> float:
    """Return peak resident set size in MB (Linux ``ru_maxrss`` in KB).

    macOS reports ``ru_maxrss`` in bytes rather than kilobytes — the
    benchmarks run in Linux CI by policy (see run_all.sh) so we assume KB;
    a macOS path would need an ``if sys.platform == "darwin"`` scale of 1024.
    """
    usage = resource.getrusage(resource.RUSAGE_SELF)
    return usage.ru_maxrss / 1024.0
