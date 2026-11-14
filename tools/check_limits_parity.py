# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
"""Enforce parity between the Agda limits and reply tags and what each binding reads.

Per AGENTS.md universal rule "Adversarial-input bounds at parser surfaces",
``src/Aletheia/Limits.agda`` is the single source of truth for every
adversarial-input bound enforced anywhere in the Aletheia stack.

Three language bindings mirror these constants for pre-FFI rejection (so
pathological inputs are rejected before being marshalled across the language
boundary) and for typed comparison by name, and a fourth mirrors the bound
kinds alone:

* ``go/aletheia/limits.go``: the cgo-boundary mirror.
* ``python/aletheia/limits.py``: the ctypes-boundary mirror.
* ``cpp/include/aletheia/limits.hpp``: the dlopen-boundary mirror.
* ``rust/src/limits.rs``: the bound kinds' wire codes and no maximum.  Rust
  reads every number into a ``u128``, which is its bound, so no table maps a
  ``max-*`` constant to it and a ``MAX_*`` constant there is a divergence.

The Go, Python and C++ headers say "Single source of truth:
src/Aletheia/Limits.agda; numeric values are mirrored here verbatim", and this
script enforces that promise on all three.

Strategy:

1. Parse the SSOT for every ``boundKindCode <Tag> = "<wire>"`` mapping and
   every ``max-<kebab-name> = <number>`` constant.
2. Parse each mirror for its own spelling of both: ``BoundKind<Tag>`` and
   ``Max<Name>`` in Go, ``BOUND_KIND_<TAG>`` and ``MAX_<NAME>`` in Python,
   ``bound_kind_<tag>`` and ``max_<name>`` in C++, and ``BOUND_KIND_<TAG>``
   alone in Rust, each a ``pub const`` of ``&str``.  Evaluate the value
   expression (``64 * 1024 * 1024`` and the like) rather than matching text.
3. Cross-check through a manual per-binding table, because kebab-case to the
   mirror's spelling is not a rule (``DBC`` and ``JSON`` stay uppercase).
4. Fail on a wire-string mismatch, a tag or constant missing from either side,
   a value mismatch, a REQUIRED constant absent from a mirror, a mirror const
   with no SSOT peer, a ``MAX_*`` constant in the Rust mirror, or an SSOT entry
   no table maps.
5. Parse ``src/Aletheia/Protocol/ReplyRange.agda`` for every ``replyText`` row
   (a place and its word set, or any non-empty text) and every
   ``replyNonEmpty`` row, and fail on a row ``PYTHON_REPLY_TEXT``,
   ``GO_REPLY_TEXT``, ``CPP_REPLY_TEXT``, ``RUST_REPLY_TEXT`` or
   ``REPLY_NON_EMPTY`` names that the Agda drops, an Agda row they do not name,
   a word one side holds and the other does not (Python's set read from its
   ``Literal`` alias, the ``Literal`` field of a class or of a union of
   classes, its ``StrEnum``, the literals a reader's ``field_word`` calls
   await, an ``if`` testing the one call's word against a literal its arm and
   the code after it its last arm, or its ``BOUND_KIND_*`` codes; Go's from the
   literals a reader's ``fieldWord`` calls await, the one ``var`` block of a
   struct type's values, which no line elsewhere may build or reach, or its
   ``BoundKind*`` codes; C++'s from a ``std::to_array`` table of ``{word,
   enumerator}`` pairs, the literals a dispatch compares a word with, the
   literals its ``field_word`` calls await, the words one function gives an
   enum's enumerators, which no line elsewhere may give or reach, or its
   ``bound_kind_*`` codes; Rust's from the string-literal arms of a function's
   one ``match`` on its word, whose final ``_`` arm reads as the word of an arm
   building the variant it builds, the literals its ``field_word`` calls
   await, the words one method gives an enum's variants, which no line
   elsewhere may give or reach, or its ``BOUND_KIND_*`` codes), a last arm
   other than the row's last word, a ``bound_kind`` row that differs
   from ``boundKindCode``, or a row at a place ``GO_UNTAGGED`` or
   ``RUST_UNTAGGED`` reads past.
   The proof leaves an unlisted string place free, so this arm is what holds
   each row the readers rely on.  It lives in ``tools/_reply_places.py``, its
   Go reader in ``tools/_reply_places_go.py``, its C++ reader in
   ``tools/_reply_places_cpp.py`` and its Rust reader in
   ``tools/_reply_places_rust.py``; a clause of either table or a reader's type
   or code it cannot read, a place a table names twice, a ``replyText`` word
   that is not identifier-shaped (a Go or Rust reader's literal of another
   shape compares no word), a Go reader file comparing a word outside the
   lines its rows read and the switch and select statements of the functions
   ``GO_UNTAGGED`` names, a C++ reader file comparing a word outside the
   dispatches or looking up a table no reader file declares, and a Rust reader
   file comparing a word outside the matches and the functions
   ``RUST_UNTAGGED`` names, exit 2.

Exit codes:
  0: full parity between Agda SSOT and every mirror.
  1: at least one divergence detected.
  2: usage error / file missing / parse failure.

A constant flagged REQUIRED is one a mirror must carry; one flagged OPTIONAL,
a list-cardinality bound the kernel enforces after parsing, a mirror may omit.
The input-length, structural and value-magnitude bounds are REQUIRED, and so
are some list-cardinality bounds.  A constant in ``KERNEL_ONLY`` is a limit the
kernel alone decides and the bindings do not know: no mirror may carry it, so
no table maps it.

Changing ``MaxMessagesPerFile = 10000`` to ``9999`` in the Go mirror fires
this script; reverting returns to exit 0.
"""

from __future__ import annotations

import argparse
import ast
import re
import sys
from dataclasses import dataclass
from pathlib import Path
from typing import TYPE_CHECKING, NewType

from tools._common import emit
from tools._reply_places import (
    AGDA_REPLY_RANGE,
    PYTHON_REPLY_TEXT,
    REPLY_NON_EMPTY,
    AgdaText,
    ReplyWord,
    check_reply_places,
    python_reader,
    read_reply_tables,
)
from tools._reply_places_cpp import CPP_REPLY_TEXT, cpp_reader
from tools._reply_places_go import GO_REPLY_TEXT, go_reader, go_untagged_rows
from tools._reply_places_rust import (
    RUST_REPLY_TEXT,
    RustSymbol,
    RustText,
    rust_reader,
    rust_untagged_rows,
)

if TYPE_CHECKING:
    from collections.abc import Callable

REPO_ROOT = Path(__file__).resolve().parent.parent
AGDA_LIMITS = REPO_ROOT / "src" / "Aletheia" / "Limits.agda"
GO_LIMITS = REPO_ROOT / "go" / "aletheia" / "limits.go"
PYTHON_LIMITS = REPO_ROOT / "python" / "aletheia" / "limits.py"
CPP_LIMITS = REPO_ROOT / "cpp" / "include" / "aletheia" / "limits.hpp"
RUST_LIMITS = REPO_ROOT / "rust" / "src" / "limits.rs"


# An Agda limit's kebab-case name, as ``Aletheia.Limits`` defines it.
AgdaLimitName = NewType("AgdaLimitName", str)
# An Agda ``BoundKind`` constructor, as ``boundKindCode`` names it.
AgdaBoundKind = NewType("AgdaBoundKind", str)
# How a C++ limit spells a type's maximum, and that maximum.
CppMaximumSpelling = NewType("CppMaximumSpelling", str)
TypeMaximum = NewType("TypeMaximum", int)

# The per-field limits the kernel decides when it reads a DBC or a property and
# proves of every reply; the bindings print its refusal and mirror none of them.
KERNEL_ONLY: frozenset[AgdaLimitName] = frozenset(
    AgdaLimitName(name)
    for name in (
        "max-start-bit",
        "max-bit-length",
        "max-multiplex-value",
        "max-value-description-key-magnitude",
        "max-var-type",
        "max-attribute-magnitude",
        "max-time-bound",
    )
)


# Manual mapping from Agda kebab-case names to Go PascalCase names, each with
# its category: a REQUIRED constant absent from the Go mirror is a divergence,
# an OPTIONAL one may be absent, and a value present is compared either way.
# The kernel enforces every bound at its parser entries; the Go binding refuses
# only the input-length bounds again at the cgo boundary.  When adding a new
# Agda constant, decide its category and add it here.
NAME_MAPPING: dict[str, tuple[str, str]] = {
    # Input-length and structural bounds.
    "max-dbc-text-bytes": ("MaxDBCTextBytes", "REQUIRED"),
    "max-json-bytes": ("MaxJSONBytes", "REQUIRED"),
    "max-nesting-depth": ("MaxNestingDepth", "REQUIRED"),
    "max-identifier-length": ("MaxIdentifierLength", "REQUIRED"),
    "max-string-length-characters": ("MaxStringLengthCharacters", "REQUIRED"),
    "max-atom-count-per-property": ("MaxAtomCountPerProperty", "REQUIRED"),
    "max-properties-per-stream": ("MaxPropertiesPerStream", "REQUIRED"),
    # Value-magnitude bound: a rational's numerator magnitude and denominator,
    # each at most 2^128-1 with the sign apart, on the parsed (reduced) form.
    "max-rational-component-magnitude": ("MaxRationalComponentMagnitude", "REQUIRED"),
    # List-cardinality bounds the mirror must carry.
    "max-messages-per-file": ("MaxMessagesPerFile", "REQUIRED"),
    "max-signals-per-message": ("MaxSignalsPerMessage", "REQUIRED"),
    "max-attributes-per-file": ("MaxAttributesPerFile", "REQUIRED"),
    "max-value-descriptions-per-file": ("MaxValueDescriptionsPerFile", "REQUIRED"),
    # List-cardinality bounds the mirror may omit.
    "max-comments-per-file": ("MaxCommentsPerFile", "OPTIONAL"),
    "max-nodes-per-file": ("MaxNodesPerFile", "OPTIONAL"),
    "max-value-tables-per-file": ("MaxValueTablesPerFile", "OPTIONAL"),
    "max-signal-groups-per-file": ("MaxSignalGroupsPerFile", "OPTIONAL"),
    "max-environment-variables-per-file": ("MaxEnvironmentVariablesPerFile", "OPTIONAL"),
    "max-unresolved-value-descriptions-per-file": (
        "MaxUnresolvedValueDescriptionsPerFile",
        "OPTIONAL",
    ),
    "max-enum-labels-per-attribute": ("MaxEnumLabelsPerAttribute", "OPTIONAL"),
    "max-multiplex-values-per-signal": ("MaxMultiplexValuesPerSignal", "OPTIONAL"),
}


# Python mirror: kebab-case to SCREAMING_SNAKE, the constants and categories
# of ``NAME_MAPPING``, a REQUIRED constant absent from the Python mirror being
# a divergence.
PYTHON_NAME_MAPPING: dict[str, tuple[str, str]] = {
    "max-dbc-text-bytes": ("MAX_DBC_TEXT_BYTES", "REQUIRED"),
    "max-json-bytes": ("MAX_JSON_BYTES", "REQUIRED"),
    "max-nesting-depth": ("MAX_NESTING_DEPTH", "REQUIRED"),
    "max-identifier-length": ("MAX_IDENTIFIER_LENGTH", "REQUIRED"),
    "max-string-length-characters": ("MAX_STRING_LENGTH_CHARACTERS", "REQUIRED"),
    "max-atom-count-per-property": ("MAX_ATOM_COUNT_PER_PROPERTY", "REQUIRED"),
    "max-properties-per-stream": ("MAX_PROPERTIES_PER_STREAM", "REQUIRED"),
    "max-rational-component-magnitude": ("MAX_RATIONAL_COMPONENT_MAGNITUDE", "REQUIRED"),
    "max-messages-per-file": ("MAX_MESSAGES_PER_FILE", "REQUIRED"),
    "max-signals-per-message": ("MAX_SIGNALS_PER_MESSAGE", "REQUIRED"),
    "max-attributes-per-file": ("MAX_ATTRIBUTES_PER_FILE", "REQUIRED"),
    "max-value-descriptions-per-file": ("MAX_VALUE_DESCRIPTIONS_PER_FILE", "REQUIRED"),
    "max-comments-per-file": ("MAX_COMMENTS_PER_FILE", "OPTIONAL"),
    "max-nodes-per-file": ("MAX_NODES_PER_FILE", "OPTIONAL"),
    "max-value-tables-per-file": ("MAX_VALUE_TABLES_PER_FILE", "OPTIONAL"),
    "max-signal-groups-per-file": ("MAX_SIGNAL_GROUPS_PER_FILE", "OPTIONAL"),
    "max-environment-variables-per-file": ("MAX_ENVIRONMENT_VARIABLES_PER_FILE", "OPTIONAL"),
    "max-unresolved-value-descriptions-per-file": (
        "MAX_UNRESOLVED_VALUE_DESCRIPTIONS_PER_FILE",
        "OPTIONAL",
    ),
    "max-enum-labels-per-attribute": ("MAX_ENUM_LABELS_PER_ATTRIBUTE", "OPTIONAL"),
    "max-multiplex-values-per-signal": ("MAX_MULTIPLEX_VALUES_PER_SIGNAL", "OPTIONAL"),
}


# Python BoundKind enum: every entry's wire-code string must match between
# Agda and Python (`BOUND_KIND_*` consts in `python/aletheia/limits.py`).
PYTHON_BOUND_KIND_MAPPING: dict[str, str] = {
    "InputLengthBytes": "BOUND_KIND_INPUT_LENGTH_BYTES",
    "NestingDepth": "BOUND_KIND_NESTING_DEPTH",
    "ArrayCardinality": "BOUND_KIND_ARRAY_CARDINALITY",
    "IdentifierLength": "BOUND_KIND_IDENTIFIER_LENGTH",
    "StringLength": "BOUND_KIND_STRING_LENGTH",
    "AtomCount": "BOUND_KIND_ATOM_COUNT",
    "PropertyCount": "BOUND_KIND_PROPERTY_COUNT",
    "RationalComponentMagnitude": "BOUND_KIND_RATIONAL_COMPONENT_MAGNITUDE",
}

# C++ mirror: kebab-case to snake_case.  The header states it mirrors every
# numeric value verbatim and it carries every constant outside ``KERNEL_ONLY``,
# so each is REQUIRED: a mirror that drops one stops being the verbatim mirror
# it claims to be, whether or not the binding enforces that bound itself.
CPP_NAME_MAPPING: dict[str, tuple[str, str]] = {
    "max-dbc-text-bytes": ("max_dbc_text_bytes", "REQUIRED"),
    "max-json-bytes": ("max_json_bytes", "REQUIRED"),
    "max-nesting-depth": ("max_nesting_depth", "REQUIRED"),
    "max-identifier-length": ("max_identifier_length", "REQUIRED"),
    "max-string-length-characters": ("max_string_length_characters", "REQUIRED"),
    "max-atom-count-per-property": ("max_atom_count_per_property", "REQUIRED"),
    "max-properties-per-stream": ("max_properties_per_stream", "REQUIRED"),
    "max-rational-component-magnitude": ("max_rational_component_magnitude", "REQUIRED"),
    "max-messages-per-file": ("max_messages_per_file", "REQUIRED"),
    "max-signals-per-message": ("max_signals_per_message", "REQUIRED"),
    "max-attributes-per-file": ("max_attributes_per_file", "REQUIRED"),
    "max-value-descriptions-per-file": ("max_value_descriptions_per_file", "REQUIRED"),
    "max-comments-per-file": ("max_comments_per_file", "REQUIRED"),
    "max-nodes-per-file": ("max_nodes_per_file", "REQUIRED"),
    "max-value-tables-per-file": ("max_value_tables_per_file", "REQUIRED"),
    "max-signal-groups-per-file": ("max_signal_groups_per_file", "REQUIRED"),
    "max-environment-variables-per-file": ("max_environment_variables_per_file", "REQUIRED"),
    "max-unresolved-value-descriptions-per-file": (
        "max_unresolved_value_descriptions_per_file",
        "REQUIRED",
    ),
    "max-enum-labels-per-attribute": ("max_enum_labels_per_attribute", "REQUIRED"),
    "max-multiplex-values-per-signal": ("max_multiplex_values_per_signal", "REQUIRED"),
}


# C++ BoundKind wire codes: `bound_kind_*` string views in the mirror header.
CPP_BOUND_KIND_MAPPING: dict[str, str] = {
    "InputLengthBytes": "bound_kind_input_length_bytes",
    "NestingDepth": "bound_kind_nesting_depth",
    "ArrayCardinality": "bound_kind_array_cardinality",
    "IdentifierLength": "bound_kind_identifier_length",
    "StringLength": "bound_kind_string_length",
    "AtomCount": "bound_kind_atom_count",
    "PropertyCount": "bound_kind_property_count",
    "RationalComponentMagnitude": "bound_kind_rational_component_magnitude",
}


# Rust BoundKind wire codes: the `BOUND_KIND_*` public constants of the mirror
# module.  Rust mirrors no maximum, the u128 it reads every number into being
# its bound, so no name table maps a `max-*` constant to it.
RUST_BOUND_KIND_MAPPING: dict[AgdaBoundKind, RustSymbol] = {
    AgdaBoundKind(tag): RustSymbol(name)
    for tag, name in {
        "InputLengthBytes": "BOUND_KIND_INPUT_LENGTH_BYTES",
        "NestingDepth": "BOUND_KIND_NESTING_DEPTH",
        "ArrayCardinality": "BOUND_KIND_ARRAY_CARDINALITY",
        "IdentifierLength": "BOUND_KIND_IDENTIFIER_LENGTH",
        "StringLength": "BOUND_KIND_STRING_LENGTH",
        "AtomCount": "BOUND_KIND_ATOM_COUNT",
        "PropertyCount": "BOUND_KIND_PROPERTY_COUNT",
        "RationalComponentMagnitude": "BOUND_KIND_RATIONAL_COMPONENT_MAGNITUDE",
    }.items()
}


# BoundKind enum: every entry's wire-code string must match between Agda
# (`boundKindCode`) and Go (`BoundKind*` consts).  Mapping below pairs the
# Agda ADT tag with the Go const name.
BOUND_KIND_MAPPING: dict[str, str] = {
    "InputLengthBytes": "BoundKindInputLengthBytes",
    "NestingDepth": "BoundKindNestingDepth",
    "ArrayCardinality": "BoundKindArrayCardinality",
    "IdentifierLength": "BoundKindIdentifierLength",
    "StringLength": "BoundKindStringLength",
    "AtomCount": "BoundKindAtomCount",
    "PropertyCount": "BoundKindPropertyCount",
    "RationalComponentMagnitude": "BoundKindRationalComponentMagnitude",
}


# Whitelisted binary operators: concrete ``ast`` node type → numeric impl.
# Membership in this table is the entire authorisation surface for binary
# arithmetic — a node whose ``op`` type is absent raises in _eval_arith_node.
_BIN_OPS: dict[type[ast.operator], Callable[[float, float], float]] = {
    ast.Add: lambda a, b: a + b,
    ast.Sub: lambda a, b: a - b,
    ast.Mult: lambda a, b: a * b,
    ast.Div: lambda a, b: a / b,
    ast.FloorDiv: lambda a, b: a // b,
    ast.Mod: lambda a, b: a % b,
    ast.Pow: lambda a, b: a**b,
}

# Whitelisted unary operators: concrete ``ast`` node type → numeric impl.
_UNARY_OPS: dict[type[ast.unaryop], Callable[[float], float]] = {
    ast.USub: lambda a: -a,
    ast.UAdd: lambda a: +a,
}


# A C++ integer-literal suffix (``64ULL``): not part of the value, and not
# something Python's parser accepts.
_DIGIT_SUFFIX = re.compile(r"(?<=\d)[uUlL]+")


def _eval_arith_node(node: ast.expr) -> float:
    """Evaluate one AST node of a whitelisted arithmetic expression.

    Recursively evaluates ``node`` allowing only literal numeric constants,
    binary arithmetic (``+ - * / // % **``), and unary sign (``+ -``).  Any
    other node kind, operator, or non-numeric constant raises ``ValueError`` —
    this is the structural replacement for ``eval`` (no builtins, no names, no
    attribute/call access can ever reach evaluation).
    """
    if isinstance(node, ast.Constant):
        value = node.value
        # `bool` is an `int` subclass; reject it first so only genuine
        # number literals (int / float, never True / False) evaluate.
        if not isinstance(value, bool) and isinstance(value, int | float):
            return value
        message = f"non-numeric constant in arithmetic expression: {value!r}"
        raise ValueError(message)
    if isinstance(node, ast.BinOp):
        binary = _BIN_OPS.get(type(node.op))
        if binary is None:
            message = f"disallowed binary operator: {type(node.op).__name__}"
            raise ValueError(message)
        return binary(_eval_arith_node(node.left), _eval_arith_node(node.right))
    if isinstance(node, ast.UnaryOp):
        unary = _UNARY_OPS.get(type(node.op))
        if unary is None:
            message = f"disallowed unary operator: {type(node.op).__name__}"
            raise ValueError(message)
        return unary(_eval_arith_node(node.operand))
    message = f"disallowed expression node: {type(node).__name__}"
    raise ValueError(message)


def _eval_int_expr(expr: str) -> int | None:
    """Evaluate a small integer arithmetic expression safely, or return None.

    Parses ``expr`` via ``ast.parse(..., mode="eval")`` and walks the tree
    through ``_eval_arith_node``'s whitelist.  Each language writes the same
    number its own way, so the digit separators of Go and Python, the ones C++
    spells with an apostrophe, and a C++ integer suffix are stripped first.
    Returns the integer result, or None when the expression fails to parse,
    contains a disallowed construct, or does not reduce to an ``int`` (e.g. a
    true-division result).  The silent None return preserves the parsers'
    "skip lines that don't reduce to an integer constant" behaviour.
    """
    cleaned = _DIGIT_SUFFIX.sub("", expr.strip().replace("_", "").replace("'", ""))
    try:
        tree = ast.parse(cleaned, mode="eval")
        result = _eval_arith_node(tree.body)
    except SyntaxError, ValueError, TypeError, ZeroDivisionError:
        return None
    # Constants in this codebase are integers; reject a `float` result (e.g.
    # from `/`) so the contract stays `int | None` and matches prior behaviour.
    # `bool` cannot reach here — it is rejected at constant evaluation above.
    if isinstance(result, int):
        return result
    return None


def _read(path: Path) -> str:
    """Return the UTF-8 text of ``path``, exiting with code 2 if it is absent."""
    if not path.is_file():
        _ = sys.stderr.write(f"check-limits-parity: {path} not found\n")
        sys.exit(2)
    return path.read_text(encoding="utf-8")


def _parse_agda_limits(text: str) -> tuple[dict[str, int], dict[str, str]]:
    r"""Parse Agda Limits.agda — returns (max-constants, boundKindCode-table).

    Constants are parsed from the ``name : Nat`` then ``name = <number>``
    pattern.  Only numeric literal RHS values are extracted (no arithmetic —
    Agda Limits.agda intentionally uses literal values for readability).
    """
    # `max-name = 12345` literal-value definitions.
    const_pattern = re.compile(
        r"^(?P<name>max-[a-z0-9-]+)\s*=\s*(?P<value>\d+)\b",
        flags=re.MULTILINE,
    )
    constants: dict[str, int] = {}
    for m in const_pattern.finditer(text):
        constants[m.group("name")] = int(m.group("value"))

    # `boundKindCode <Tag> = "<wire>"` mapping.
    bkc_pattern = re.compile(
        r"^boundKindCode\s+(?P<tag>[A-Z][A-Za-z]*)\s*=\s*\"(?P<wire>[a-z_]+)\"",
        flags=re.MULTILINE,
    )
    boundkind: dict[str, str] = {}
    for m in bkc_pattern.finditer(text):
        boundkind[m.group("tag")] = m.group("wire")

    return constants, boundkind


def _parse_go_limits(text: str) -> tuple[dict[str, int], dict[str, str]]:
    """Parse Go limits.go const blocks — return (Max* constants, BoundKind* strings).

    Tolerates:
      * ``Name = 64 * 1024 * 1024`` (arithmetic with literals).
      * ``Name = 67108864`` (literal).
      * doc comments before each ``Name = …`` line.
    """
    # `MaxName = <expression>` lines — strip trailing ``//`` comment.
    max_pattern = re.compile(
        r"^\s*(?P<name>Max[A-Z][A-Za-z0-9]*)\s*=\s*(?P<expr>[^/\n]+?)\s*(?://.*)?$",
        flags=re.MULTILINE,
    )
    constants: dict[str, int] = {}
    for m in max_pattern.finditer(text):
        value = _eval_int_expr(m.group("expr"))
        if value is not None:
            constants[m.group("name")] = value

    # `BoundKindName = "wire"` lines.
    bk_pattern = re.compile(
        r"^\s*(?P<name>BoundKind[A-Z][A-Za-z0-9]*)\s*=\s*\"(?P<wire>[a-z_]+)\"",
        flags=re.MULTILINE,
    )
    boundkind: dict[str, str] = {}
    for m in bk_pattern.finditer(text):
        boundkind[m.group("name")] = m.group("wire")

    return constants, boundkind


def _parse_python_limits(text: str) -> tuple[dict[str, int], dict[str, str]]:
    """Parse Python limits.py — return (MAX_* constants, BOUND_KIND_* strings).

    Recognises:
      * ``MAX_NAME: Final[Limit] = 64 * 1024 * 1024``, with any type name in the
        brackets, a bare ``Final``, or no annotation at all.
      * ``BOUND_KIND_NAME: Final = BoundKind("wire")``, the same annotations
        allowed, and the code either wrapped in a ``NewType`` call or bare.
    """
    final = r"(?::\s*Final(?:\[[A-Za-z_][A-Za-z0-9_]*\])?)?"
    max_pattern = re.compile(
        rf"^\s*(?P<name>MAX_[A-Z][A-Z0-9_]*)\s*{final}\s*=\s*" + r"(?P<expr>[^#\n]+?)\s*(?:#.*)?$",
        flags=re.MULTILINE,
    )
    constants: dict[str, int] = {}
    for m in max_pattern.finditer(text):
        value = _eval_int_expr(m.group("expr"))
        if value is not None:
            constants[m.group("name")] = value

    bk_pattern = re.compile(
        rf"^\s*(?P<name>BOUND_KIND_[A-Z][A-Z0-9_]*)\s*{final}\s*="
        + r'\s*(?:[A-Za-z_][A-Za-z0-9_]*\(\s*)?"(?P<wire>[a-z_]+)"',
        flags=re.MULTILINE,
    )
    boundkind: dict[str, str] = {}
    for m in bk_pattern.finditer(text):
        boundkind[m.group("name")] = m.group("wire")

    return constants, boundkind


# The maxima a C++ limit spells through ``std::numeric_limits``, in place of
# the literal C++ cannot write past 64 bits.
_CPP_TYPE_MAXIMA: dict[CppMaximumSpelling, TypeMaximum] = {
    CppMaximumSpelling("std::numeric_limits<std::uint64_t>::max()"): TypeMaximum(2**64 - 1),
    CppMaximumSpelling("std::numeric_limits<unsigned __int128>::max()"): TypeMaximum(2**128 - 1),
}


def _parse_cpp_limits(text: str) -> tuple[dict[str, int], dict[str, str]]:
    """Parse the C++ limits header, returning (max_* constants, bound_kind_* strings).

    Recognises ``inline constexpr std::uint64_t max_name = <expression>;``, the
    same with ``auto`` where the initializer fixes the type, and ``inline
    constexpr std::string_view bound_kind_name = "wire";``.  C++ has no literal
    past 64 bits, so a type's ``std::numeric_limits<T>::max()`` reads as that
    type's maximum.  Both patterns span lines because the formatter wraps a long
    one onto the next.
    """
    max_pattern = re.compile(
        r"^inline constexpr (?:std::uint64_t|auto)\s+(?P<name>max_[a-z0-9_]+)"
        + r"\s*=\s*(?P<expr>[^;]+);",
        flags=re.MULTILINE,
    )
    constants: dict[str, int] = {}
    for m in max_pattern.finditer(text):
        expr = m.group("expr")
        for spelling, maximum in _CPP_TYPE_MAXIMA.items():
            expr = expr.replace(spelling, f"({maximum})")
        value = _eval_int_expr(expr)
        if value is not None:
            constants[m.group("name")] = value

    bk_pattern = re.compile(
        r"inline constexpr std::string_view\s+(?P<name>bound_kind_[a-z0-9_]+)\s*=\s*"
        + r'"(?P<wire>[a-z_]+)"',
        flags=re.DOTALL,
    )
    boundkind: dict[str, str] = {}
    for m in bk_pattern.finditer(text):
        boundkind[m.group("name")] = m.group("wire")

    return constants, boundkind


def _parse_rust_limits(
    text: RustText,
) -> tuple[list[RustSymbol], dict[RustSymbol, ReplyWord]]:
    """Parse the Rust limits module, returning (MAX_* constant names, BOUND_KIND_* strings).

    Recognises ``pub const BOUND_KIND_NAME: &str = "wire";``, wrapped onto the
    next line too; a constant that is not ``pub``, or not a ``&str``, is not
    one.  Every ``MAX_*`` constant, of any visibility, is named, the mirror
    carrying none.
    """
    bk_pattern = re.compile(
        r"^\s*pub\s+const\s+(?P<name>BOUND_KIND_[A-Z0-9_]+)\s*:\s*&(?:'static\s+)?str\s*=\s*"
        + r'"(?P<wire>[a-z_]+)"\s*;',
        flags=re.MULTILINE,
    )
    boundkind = {
        RustSymbol(m.group("name")): ReplyWord(m.group("wire")) for m in bk_pattern.finditer(text)
    }
    max_pattern = re.compile(
        r"^\s*(?:pub(?:\([^)]*\))?\s+)?const\s+(?P<name>MAX_[A-Z0-9_]*)\b", flags=re.MULTILINE
    )
    return [RustSymbol(m.group("name")) for m in max_pattern.finditer(text)], boundkind


@dataclass(frozen=True)
class _BoundKindCheck:
    """Static configuration for one binding's BoundKind wire-code comparison.

    Bundles the per-binding labels and the Agda-tag → mirror-const mapping so
    the comparison routine takes the parsed dicts as its only varying inputs.
    """

    label: str
    mapping: dict[str, str]
    table_name: str
    binding: str


@dataclass(frozen=True)
class _NumericCheck:
    """Static configuration for one binding's numeric-constant comparison.

    Bundles the per-binding labels, the Agda-name → (mirror-const, category)
    mapping, and the ``required_reason`` and ``header_path`` a REQUIRED-missing
    message cites, leaving the parsed dicts as the only inputs.  The reason is
    per binding because the bindings hold their mirrors for different ends: two
    refuse at the language boundary, one promises a verbatim copy.
    """

    label: str
    mapping: dict[str, tuple[str, str]]
    table_name: str
    binding: str
    required_reason: str
    header_path: str


def _check_boundkind_parity(
    cfg: _BoundKindCheck,
    agda_boundkind: dict[str, str],
    mirror_boundkind: dict[str, str],
) -> list[str]:
    """Return wire-code parity divergences between Agda and one binding mirror.

    Compares every Agda BoundKind tag against its mirrored ``BoundKind*`` /
    ``BOUND_KIND_*`` const named in ``cfg.mapping``, then reports any mirror
    const that the mapping does not account for (a mirror-side const without an
    Agda peer).  ``cfg.label`` prefixes each message (e.g. ``"BoundKind"`` for
    Go, ``"Python BoundKind"`` for Python); ``cfg.binding`` names the mirror.
    """
    diffs: list[str] = []
    for agda_tag, mirror_name in cfg.mapping.items():
        agda_wire = agda_boundkind.get(agda_tag)
        mirror_wire = mirror_boundkind.get(mirror_name)
        if agda_wire is None:
            diffs.append(f"{cfg.label}: Agda missing entry for tag '{agda_tag}'")
            continue
        if mirror_wire is None:
            diffs.append(f"{cfg.label}: {cfg.binding} missing entry for const '{mirror_name}'")
            continue
        if agda_wire != mirror_wire:
            diffs.append(
                f"{cfg.label} {agda_tag} / {mirror_name}: wire mismatch — "
                + f"Agda='{agda_wire}' vs {cfg.binding}='{mirror_wire}'"
            )

    mapped = set(cfg.mapping.values())
    diffs.extend(
        f"{cfg.label}: {cfg.binding} has const '{name}' (wire='{wire}') "
        + f"but {cfg.table_name} in check_limits_parity.py has no entry — "
        + f"this is a {cfg.binding}-side const without an Agda peer; either add the "
        + f"Agda entry or remove the {cfg.binding} const"
        for name, wire in mirror_boundkind.items()
        if name not in mapped
    )
    return diffs


def _check_numeric_parity(
    cfg: _NumericCheck,
    agda_consts: dict[str, int],
    mirror_consts: dict[str, int],
) -> list[str]:
    """Return numeric-constant parity divergences between Agda and one mirror.

    Compares every Agda ``max-*`` constant against its mirrored ``Max*`` /
    ``MAX_*`` peer named in ``cfg.mapping``, flagging value mismatches and
    missing REQUIRED peers (an OPTIONAL peer may be absent).  Then reports any
    mirror const the mapping does not account for (a stale mirror).
    """
    diffs: list[str] = []
    for agda_name, (mirror_name, category) in cfg.mapping.items():
        agda_val = agda_consts.get(agda_name)
        mirror_val = mirror_consts.get(mirror_name)
        if agda_val is None:
            diffs.append(f"{cfg.label}: Agda missing '{agda_name}'")
            continue
        if mirror_val is None and category == "REQUIRED":
            diffs.append(
                f"{cfg.label}: {cfg.binding} missing '{mirror_name}' "
                + f"(Agda has '{agda_name}={agda_val}'); marked REQUIRED because "
                + f"{cfg.required_reason}, see {cfg.header_path} header"
            )
            continue
        if mirror_val is not None and agda_val != mirror_val:
            diffs.append(
                f"{cfg.label} {agda_name} / {mirror_name}: value mismatch — "
                + f"Agda={agda_val} vs {cfg.binding}={mirror_val}"
            )

    mapped = {pair[0] for pair in cfg.mapping.values()}
    diffs.extend(
        f"{cfg.label}: {cfg.binding} has '{name}={value}' "
        + f"but {cfg.table_name} in check_limits_parity.py has no entry — "
        + f"this is a {cfg.binding}-side const without an Agda peer; either add "
        + f"the Agda entry (SSOT first) or remove the {cfg.binding} const"
        for name, value in mirror_consts.items()
        if name not in mapped
    )
    return diffs


def _check_agda_drift(agda_consts: dict[str, int], agda_boundkind: dict[str, str]) -> list[str]:
    """Return divergences for Agda entries absent from the cross-check tables.

    The mapping tables are keyed by Agda name, so an Agda ``boundKindCode`` tag
    or ``max-*`` constant added to the SSOT without a matching table entry would
    silently escape every binding comparison; surface it as drift on the Agda
    side so a new SSOT constant cannot slip past the gate unmapped.
    """
    diffs: list[str] = []
    diffs.extend(
        f"BoundKind: Agda has tag '{tag}' (wire='{wire}') "
        + "but BOUND_KIND_MAPPING in check_limits_parity.py has no entry — add it"
        for tag, wire in agda_boundkind.items()
        if tag not in BOUND_KIND_MAPPING
    )
    diffs.extend(
        f"max-constant: Agda has '{name}={value}' "
        + "but NAME_MAPPING in check_limits_parity.py has no entry — "
        + "add it (REQUIRED if input-size / structural, OPTIONAL if "
        + "list-cardinality enforced kernel-only), or name it in KERNEL_ONLY "
        + "if no binding may know it"
        for name, value in agda_consts.items()
        if name not in NAME_MAPPING and name not in KERNEL_ONLY
    )
    diffs.extend(
        f"max-constant: KERNEL_ONLY names '{name}', which Agda does not define"
        for name in sorted(KERNEL_ONLY - agda_consts.keys())
    )
    diffs.extend(
        f"max-constant: '{name}' is KERNEL_ONLY but {table} maps it to a mirror"
        for table, mapping in (
            ("NAME_MAPPING", NAME_MAPPING),
            ("PYTHON_NAME_MAPPING", PYTHON_NAME_MAPPING),
            ("CPP_NAME_MAPPING", CPP_NAME_MAPPING),
        )
        for name in sorted(KERNEL_ONLY & mapping.keys())
    )
    return diffs


def main() -> int:
    """Check Agda Limits SSOT parity against the Go, Python, C++ and Rust mirrors."""
    argparse.ArgumentParser(description=__doc__).parse_args()  # no options; --help only
    agda_consts, agda_boundkind = _parse_agda_limits(_read(AGDA_LIMITS))
    go_consts, go_boundkind = _parse_go_limits(_read(GO_LIMITS))
    py_consts, py_boundkind = _parse_python_limits(_read(PYTHON_LIMITS))
    cpp_consts, cpp_boundkind = _parse_cpp_limits(_read(CPP_LIMITS))
    rust_maxima, rust_boundkind = _parse_rust_limits(RustText(_read(RUST_LIMITS)))

    if not agda_consts:
        _ = sys.stderr.write("check-limits-parity: no max-* constants parsed from Limits.agda\n")
        return 2
    if not agda_boundkind:
        _ = sys.stderr.write(
            "check-limits-parity: no boundKindCode entries parsed from Limits.agda\n"
        )
        return 2

    diffs: list[str] = []
    # 1) Go BoundKind wire-code parity.
    diffs.extend(
        _check_boundkind_parity(
            _BoundKindCheck(
                label="BoundKind",
                mapping=BOUND_KIND_MAPPING,
                table_name="BOUND_KIND_MAPPING",
                binding="Go",
            ),
            agda_boundkind,
            go_boundkind,
        )
    )
    # 2) Go numeric constant parity.
    diffs.extend(
        _check_numeric_parity(
            _NumericCheck(
                label="max-constant",
                mapping=NAME_MAPPING,
                table_name="NAME_MAPPING",
                binding="Go",
                required_reason=(
                    "every REQUIRED bound is refused at the cgo boundary before the buffer crosses"
                ),
                header_path="go/aletheia/limits.go",
            ),
            agda_consts,
            go_consts,
        )
    )
    # 3) Python BoundKind wire-code parity.
    diffs.extend(
        _check_boundkind_parity(
            _BoundKindCheck(
                label="Python BoundKind",
                mapping=PYTHON_BOUND_KIND_MAPPING,
                table_name="PYTHON_BOUND_KIND_MAPPING",
                binding="Python",
            ),
            agda_boundkind,
            py_boundkind,
        )
    )
    # 4) Python numeric constant parity.
    diffs.extend(
        _check_numeric_parity(
            _NumericCheck(
                label="Python max-constant",
                mapping=PYTHON_NAME_MAPPING,
                table_name="PYTHON_NAME_MAPPING",
                binding="Python",
                required_reason=(
                    "every REQUIRED bound is refused at the ctypes boundary "
                    "before the buffer crosses"
                ),
                header_path="python/aletheia/limits.py",
            ),
            agda_consts,
            py_consts,
        )
    )
    # 5) C++ BoundKind wire-code parity.
    diffs.extend(
        _check_boundkind_parity(
            _BoundKindCheck(
                label="C++ BoundKind",
                mapping=CPP_BOUND_KIND_MAPPING,
                table_name="CPP_BOUND_KIND_MAPPING",
                binding="C++",
            ),
            agda_boundkind,
            cpp_boundkind,
        )
    )
    # 6) C++ numeric constant parity.
    diffs.extend(
        _check_numeric_parity(
            _NumericCheck(
                label="C++ max-constant",
                mapping=CPP_NAME_MAPPING,
                table_name="CPP_NAME_MAPPING",
                binding="C++",
                required_reason="the header mirrors every value verbatim",
                header_path="cpp/include/aletheia/limits.hpp",
            ),
            agda_consts,
            cpp_consts,
        )
    )
    # 7) Rust BoundKind wire-code parity, the shared check reading plain strings,
    # and no maximum in the Rust mirror.
    diffs.extend(
        _check_boundkind_parity(
            _BoundKindCheck(
                label="Rust BoundKind",
                mapping={str(tag): str(name) for tag, name in RUST_BOUND_KIND_MAPPING.items()},
                table_name="RUST_BOUND_KIND_MAPPING",
                binding="Rust",
            ),
            agda_boundkind,
            {str(name): str(wire) for name, wire in rust_boundkind.items()},
        )
    )
    diffs.extend(
        f"Rust max-constant: {RUST_LIMITS.relative_to(REPO_ROOT)} declares '{name}', but Rust "
        + "mirrors no maximum, the u128 it reads every number into being its bound; remove it"
        for name in rust_maxima
    )
    # Agda-side drift: SSOT entries with no cross-check table mapping.
    diffs.extend(_check_agda_drift(agda_consts, agda_boundkind))
    # 8) The reply proof's tag and non-empty places against the Python, Go, C++ and Rust
    # readers.
    tables = read_reply_tables(
        AgdaText(_read(AGDA_REPLY_RANGE)),
        (
            python_reader(frozenset(ReplyWord(wire) for wire in py_boundkind.values())),
            go_reader(frozenset(ReplyWord(wire) for wire in go_boundkind.values())),
            cpp_reader(frozenset(ReplyWord(wire) for wire in cpp_boundkind.values())),
            rust_reader(frozenset(rust_boundkind.values())),
        ),
    )
    if isinstance(tables, list):
        for unread in tables:
            _ = sys.stderr.write(f"check-limits-parity: {unread}\n")
        return 2
    diffs.extend(
        check_reply_places(tables, frozenset(ReplyWord(wire) for wire in agda_boundkind.values()))
    )
    diffs.extend(go_untagged_rows(tables.agda_text.keys()))
    diffs.extend(rust_untagged_rows(tables.agda_text.keys()))

    if diffs:
        _ = sys.stderr.write("check-limits-parity: divergences detected\n\n")
        for d in diffs:
            _ = sys.stderr.write(f"  - {d}\n")
        mirrors = " / ".join(
            str(path.relative_to(REPO_ROOT))
            for path in (GO_LIMITS, PYTHON_LIMITS, CPP_LIMITS, RUST_LIMITS)
        )
        _ = sys.stderr.write(
            f"\nfound {len(diffs)} divergence(s) between "
            + f"{AGDA_LIMITS.relative_to(REPO_ROOT)} and "
            + f"{AGDA_REPLY_RANGE.relative_to(REPO_ROOT)} (SSOT) and "
            + f"{mirrors} and the Python, Go, C++ and Rust reply readers (mirrors).\n"
            + "Reconcile by updating the mirror, the Agda SSOT, or the mapping table "
            + "this script names above (when a constant is intentionally added or "
            + "removed).\n"
        )
        return 1

    emit(
        "check-limits-parity: "
        + "; ".join(
            f"{binding} {len(numeric)} numeric + {len(kinds)} BoundKind"
            for binding, numeric, kinds in (
                ("Go", NAME_MAPPING, BOUND_KIND_MAPPING),
                ("Python", PYTHON_NAME_MAPPING, PYTHON_BOUND_KIND_MAPPING),
                ("C++", CPP_NAME_MAPPING, CPP_BOUND_KIND_MAPPING),
            )
        )
        + f"; Rust {len(RUST_BOUND_KIND_MAPPING)} BoundKind"
        + f"; Python {len(PYTHON_REPLY_TEXT)}, Go {len(GO_REPLY_TEXT)}"
        + f", C++ {len(CPP_REPLY_TEXT)} and Rust {len(RUST_REPLY_TEXT)} reply text"
        + f" + {len(REPLY_NON_EMPTY)} non-empty places"
        + ": all in parity with Agda SSOT"
    )
    return 0


if __name__ == "__main__":
    sys.exit(main())
