# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
"""Adversarial-input bounds — Python mirror of ``Aletheia.Limits`` (Agda).

Single source of truth: ``src/Aletheia/Limits.agda`` (numeric values are
mirrored here verbatim).  Wire spec: ``docs/architecture/PROTOCOL.md § Limits``.

Parity with the SSOT is enforced by ``tools/check_limits_parity.py`` (also
invoked as ``cabal run shake -- check-limits-parity``); see ``PYTHON_NAME_MAPPING``
and ``PYTHON_BOUND_KIND_MAPPING`` in that tool for the kebab-case ↔
SCREAMING_SNAKE_CASE mapping table. The gate walks the Go, Python and C++
mirrors, so none can drift from the Agda SSOT.

The Aletheia Agda kernel enforces these bounds, all but ``MAX_DBC_TEXT_BYTES``,
which caps a file or text the binding reads: the kernel receives a DBC text
inside a JSON command, which ``MAX_JSON_BYTES`` bounds.  The binding refuses
an oversize input before the FFI boundary, so a 100 MB JSON payload is not
marshaled across ctypes only to be rejected on the other side.

Per AGENTS.md universal rule "Adversarial-input bounds at parser surfaces",
rejection over a bound is a typed :class:`InputBoundExceededError` carrying
the offending kind, the observed value, the limit it crossed and, for a
DBC's size bounds, the field that crossed it.
"""

from typing import Final, NewType

from aletheia.common_types import PositiveInt

# A bound's limit: the largest length, depth, count or magnitude an input may have.
type Limit = PositiveInt

# The wire code naming the kind of bound an input crossed.
BoundKind = NewType("BoundKind", str)

# The part of a DBC a size-bound refusal names, as the kernel spells it
# (``"senders array"``, ``"version string"``).
BoundField = NewType("BoundField", str)

# ============================================================================
# BOUND KIND CODES
# ============================================================================

# Wire codes — must match ``boundKindCode`` in ``Aletheia.Limits`` (Agda).
BOUND_KIND_INPUT_LENGTH_BYTES: Final = BoundKind("input_length_bytes")
BOUND_KIND_NESTING_DEPTH: Final = BoundKind("nesting_depth")
BOUND_KIND_ARRAY_CARDINALITY: Final = BoundKind("array_cardinality")
BOUND_KIND_IDENTIFIER_LENGTH: Final = BoundKind("identifier_length")
BOUND_KIND_STRING_LENGTH: Final = BoundKind("string_length")
BOUND_KIND_ATOM_COUNT: Final = BoundKind("atom_count")
BOUND_KIND_PROPERTY_COUNT: Final = BoundKind("property_count")
BOUND_KIND_RATIONAL_COMPONENT_MAGNITUDE: Final = BoundKind("rational_component_magnitude")

# ============================================================================
# BOUND CONSTANTS
# ============================================================================

# A DBC text file's length in bytes, the binding's cap on a file or text it
# reads.  64 MiB.
MAX_DBC_TEXT_BYTES: Final[Limit] = 64 * 1024 * 1024

# Total JSON input length in bytes (FFI boundary).  64 MiB.
MAX_JSON_BYTES: Final[Limit] = 64 * 1024 * 1024

# JSON object/array nesting depth.
MAX_NESTING_DEPTH: Final[Limit] = 64

# DBC messages per file.
MAX_MESSAGES_PER_FILE: Final[Limit] = 10_000

# Signals per single DBC message, and members of one signal group, which are
# one message's signals.
MAX_SIGNALS_PER_MESSAGE: Final[Limit] = 1024

# Attribute definitions / assignments per DBC file.
MAX_ATTRIBUTES_PER_FILE: Final[Limit] = 10_000

# Value-description entries per DBC file, whether they sit in a table, on a
# signal or on a line naming no signal.
MAX_VALUE_DESCRIPTIONS_PER_FILE: Final[Limit] = 1_000_000

# Comments per DBC file.
MAX_COMMENTS_PER_FILE: Final[Limit] = 10_000

# Nodes per DBC file, senders of one message and receivers of one signal.
MAX_NODES_PER_FILE: Final[Limit] = 10_000

# Value tables per DBC file.
MAX_VALUE_TABLES_PER_FILE: Final[Limit] = 10_000

# Signal groups per DBC file.
MAX_SIGNAL_GROUPS_PER_FILE: Final[Limit] = 10_000

# Environment variables per DBC file.
MAX_ENVIRONMENT_VARIABLES_PER_FILE: Final[Limit] = 10_000

# Value-description lines per DBC file naming no signal of it, counted as
# lines rather than entries.
MAX_UNRESOLVED_VALUE_DESCRIPTIONS_PER_FILE: Final[Limit] = 10_000

# Labels of one enumerated attribute type.
MAX_ENUM_LABELS_PER_ATTRIBUTE: Final[Limit] = 10_000

# Selector values one multiplexed signal is present for.
MAX_MULTIPLEX_VALUES_PER_SIGNAL: Final[Limit] = 1024

# DBC identifier (signal name, message name, etc.) length in characters.
MAX_IDENTIFIER_LENGTH: Final[Limit] = 128

# A DBC text field's length in characters.
MAX_STRING_LENGTH_CHARACTERS: Final[Limit] = 64 * 1024

# LTL atoms per single property.
MAX_ATOM_COUNT_PER_PROPERTY: Final[Limit] = 1024

# LTL properties submittable in one setProperties call.
MAX_PROPERTIES_PER_STREAM: Final[Limit] = 1024

# Magnitude cap on a JSON number's rational components (|numerator| and
# denominator of the exact rational it denotes): the signed 64-bit wire
# range shared with the binary FFI's rational slots and the decimal SSOT.
MAX_RATIONAL_COMPONENT_MAGNITUDE: Final[Limit] = 9223372036854775807


__all__ = [
    "BOUND_KIND_ARRAY_CARDINALITY",
    "BOUND_KIND_ATOM_COUNT",
    "BOUND_KIND_IDENTIFIER_LENGTH",
    "BOUND_KIND_INPUT_LENGTH_BYTES",
    "BOUND_KIND_NESTING_DEPTH",
    "BOUND_KIND_PROPERTY_COUNT",
    "BOUND_KIND_RATIONAL_COMPONENT_MAGNITUDE",
    "BOUND_KIND_STRING_LENGTH",
    "MAX_ATOM_COUNT_PER_PROPERTY",
    "MAX_ATTRIBUTES_PER_FILE",
    "MAX_COMMENTS_PER_FILE",
    "MAX_DBC_TEXT_BYTES",
    "MAX_ENUM_LABELS_PER_ATTRIBUTE",
    "MAX_ENVIRONMENT_VARIABLES_PER_FILE",
    "MAX_IDENTIFIER_LENGTH",
    "MAX_JSON_BYTES",
    "MAX_MESSAGES_PER_FILE",
    "MAX_MULTIPLEX_VALUES_PER_SIGNAL",
    "MAX_NESTING_DEPTH",
    "MAX_NODES_PER_FILE",
    "MAX_PROPERTIES_PER_STREAM",
    "MAX_RATIONAL_COMPONENT_MAGNITUDE",
    "MAX_SIGNALS_PER_MESSAGE",
    "MAX_SIGNAL_GROUPS_PER_FILE",
    "MAX_STRING_LENGTH_CHARACTERS",
    "MAX_UNRESOLVED_VALUE_DESCRIPTIONS_PER_FILE",
    "MAX_VALUE_DESCRIPTIONS_PER_FILE",
    "MAX_VALUE_TABLES_PER_FILE",
    "BoundField",
    "BoundKind",
    "Limit",
]
