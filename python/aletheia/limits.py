# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
"""Adversarial-input bounds — Python mirror of ``Aletheia.Limits`` (Agda).

Single source of truth: ``src/Aletheia/Limits.agda`` (numeric values are
mirrored here verbatim).  Wire spec: ``docs/architecture/PROTOCOL.md § Limits``.

Parity with the SSOT is enforced by ``tools/check_limits_parity.py`` (also
invoked as ``cabal run shake -- check-limits-parity``); see ``PYTHON_NAME_MAPPING``
and ``PYTHON_BOUND_KIND_MAPPING`` in that tool for the kebab-case ↔
SCREAMING_SNAKE_CASE mapping table. The gate walks the Python mirror in
addition to the Go mirror, so neither can drift from the Agda SSOT.

The Aletheia Agda kernel enforces these bounds at every parser entry; this
module additionally rejects oversize inputs at the FFI boundary so a 100 MB
JSON payload is not marshaled across ctypes only to be rejected on the
other side.

Per AGENTS.md universal rule "Adversarial-input bounds at parser surfaces",
rejection over a bound is a typed :class:`InputBoundExceededError` carrying
the offending kind, the observed value, and the limit it crossed.
"""

from typing import Final

# ============================================================================
# BOUND KIND CODES
# ============================================================================

# Wire codes — must match ``boundKindCode`` in ``Aletheia.Limits`` (Agda).
BOUND_KIND_INPUT_LENGTH_BYTES: Final[str] = "input_length_bytes"
BOUND_KIND_NESTING_DEPTH: Final[str] = "nesting_depth"
BOUND_KIND_ARRAY_CARDINALITY: Final[str] = "array_cardinality"
BOUND_KIND_IDENTIFIER_LENGTH: Final[str] = "identifier_length"
BOUND_KIND_STRING_LENGTH: Final[str] = "string_length"
BOUND_KIND_ATOM_COUNT: Final[str] = "atom_count"
BOUND_KIND_FRAME_BYTE_COUNT: Final[str] = "frame_byte_count"
BOUND_KIND_PROPERTY_COUNT: Final[str] = "property_count"
BOUND_KIND_RATIONAL_COMPONENT_MAGNITUDE: Final[str] = "rational_component_magnitude"

# ============================================================================
# BOUND CONSTANTS
# ============================================================================

# Total DBC-text input length in bytes.  64 MiB.
MAX_DBC_TEXT_BYTES: Final[int] = 64 * 1024 * 1024

# Total JSON input length in bytes (FFI boundary).  64 MiB.
MAX_JSON_BYTES: Final[int] = 64 * 1024 * 1024

# JSON object/array nesting depth.
MAX_NESTING_DEPTH: Final[int] = 64

# DBC messages per file.
MAX_MESSAGES_PER_FILE: Final[int] = 10_000

# Signals per single DBC message.
MAX_SIGNALS_PER_MESSAGE: Final[int] = 1024

# Attribute definitions / assignments per DBC file.
MAX_ATTRIBUTES_PER_FILE: Final[int] = 10_000

# Value-description entries per DBC file (VAL_ + VAL_TABLE_).
MAX_VALUE_DESCRIPTIONS_PER_FILE: Final[int] = 1_000_000

# DBC identifier (signal name, message name, etc.) length in characters.
MAX_IDENTIFIER_LENGTH: Final[int] = 128

# Quoted-string body (comment text, attribute string value) length in bytes.
MAX_STRING_LENGTH_BYTES: Final[int] = 64 * 1024

# LTL atoms per single property.
MAX_ATOM_COUNT_PER_PROPERTY: Final[int] = 1024

# LTL properties submittable in one setProperties call.  Mirrors
# src/Aletheia/Limits.agda.
MAX_PROPERTIES_PER_STREAM: Final[int] = 1024

# CAN frame payload byte count (CAN-FD maximum).
MAX_FRAME_BYTE_COUNT: Final[int] = 64

# Magnitude cap on a JSON number's rational components (|numerator| and
# denominator of the exact rational it denotes): the signed 64-bit wire
# range shared with the binary FFI's rational slots and the decimal SSOT.
MAX_RATIONAL_COMPONENT_MAGNITUDE: Final[int] = 9223372036854775807


__all__ = [
    "BOUND_KIND_ARRAY_CARDINALITY",
    "BOUND_KIND_ATOM_COUNT",
    "BOUND_KIND_FRAME_BYTE_COUNT",
    "BOUND_KIND_IDENTIFIER_LENGTH",
    "BOUND_KIND_INPUT_LENGTH_BYTES",
    "BOUND_KIND_NESTING_DEPTH",
    "BOUND_KIND_PROPERTY_COUNT",
    "BOUND_KIND_RATIONAL_COMPONENT_MAGNITUDE",
    "BOUND_KIND_STRING_LENGTH",
    "MAX_ATOM_COUNT_PER_PROPERTY",
    "MAX_ATTRIBUTES_PER_FILE",
    "MAX_DBC_TEXT_BYTES",
    "MAX_FRAME_BYTE_COUNT",
    "MAX_IDENTIFIER_LENGTH",
    "MAX_JSON_BYTES",
    "MAX_MESSAGES_PER_FILE",
    "MAX_NESTING_DEPTH",
    "MAX_PROPERTIES_PER_STREAM",
    "MAX_RATIONAL_COMPONENT_MAGNITUDE",
    "MAX_SIGNALS_PER_MESSAGE",
    "MAX_STRING_LENGTH_BYTES",
    "MAX_VALUE_DESCRIPTIONS_PER_FILE",
]
