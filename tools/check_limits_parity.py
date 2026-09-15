# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
"""tools/check_limits_parity.py — Enforce parity between Agda Limits SSOT and binding mirrors.

Per AGENTS.md universal rule "Adversarial-input bounds at parser surfaces",
``src/Aletheia/Limits.agda`` is the single source of truth for every
adversarial-input bound enforced anywhere in the Aletheia stack.

Three language bindings mirror these constants for pre-FFI rejection (so
pathological inputs are rejected before being marshalled across the language
boundary) and for typed comparison by name:

* ``go/aletheia/limits.go``: the cgo-boundary mirror.
* ``python/aletheia/limits.py``: the ctypes-boundary mirror.
* ``cpp/include/aletheia/limits.hpp``: the dlopen-boundary mirror.

Each mirror's header says "Single source of truth: src/Aletheia/Limits.agda;
numeric values are mirrored here verbatim", and this script enforces that
promise on all three.

Strategy:

1. Parse the SSOT for every ``boundKindCode <Tag> = "<wire>"`` mapping and
   every ``max-<kebab-name> = <number>`` constant.
2. Parse each mirror for its own spelling of both: ``BoundKind<Tag>`` and
   ``Max<Name>`` in Go, ``BOUND_KIND_<TAG>`` and ``MAX_<NAME>`` in Python,
   ``bound_kind_<tag>`` and ``max_<name>`` in C++.  Evaluate the value
   expression (``64 * 1024 * 1024`` and the like) rather than matching text.
3. Cross-check through a manual per-binding table, because kebab-case to the
   mirror's spelling is not a rule (``DBC`` and ``JSON`` stay uppercase).
4. Fail on a wire-string mismatch, a tag or constant missing from either side,
   a value mismatch, a REQUIRED constant absent from a mirror, a mirror const
   with no SSOT peer, or an SSOT entry no table maps.

Exit codes:
  0: full parity between Agda SSOT and every mirror.
  1: at least one divergence detected.
  2: usage error / file missing / parse failure.

A constant flagged OPTIONAL is a list-cardinality bound the kernel enforces
after parsing, so a mirror may omit it: pre-rejection at the language boundary
buys nothing there.  A REQUIRED constant is an input-length or structural
bound, where refusing before the buffer crosses is strictly preferable.

Changing ``MaxMessagesPerFile = 10000`` to ``9999`` in the Go mirror fires
this script; reverting returns to exit 0.
"""

from __future__ import annotations

import ast
import re
import sys
from dataclasses import dataclass
from pathlib import Path
from typing import TYPE_CHECKING

from tools._common import emit

if TYPE_CHECKING:
    from collections.abc import Callable

REPO_ROOT = Path(__file__).resolve().parent.parent
AGDA_LIMITS = REPO_ROOT / "src" / "Aletheia" / "Limits.agda"
GO_LIMITS = REPO_ROOT / "go" / "aletheia" / "limits.go"
PYTHON_LIMITS = REPO_ROOT / "python" / "aletheia" / "limits.py"
CPP_LIMITS = REPO_ROOT / "cpp" / "include" / "aletheia" / "limits.hpp"


# Manual mapping from Agda kebab-case names to Go PascalCase names.
# REQUIRED constants must have a Go mirror; OPTIONAL constants are list-
# cardinality bounds enforced at the kernel only (no cgo-boundary advantage).
# When adding a new Agda constant, decide its category and add it here.
NAME_MAPPING: dict[str, tuple[str, str]] = {
    # Input-size bounds — REQUIRED at cgo boundary
    "max-dbc-text-bytes": ("MaxDBCTextBytes", "REQUIRED"),
    "max-json-bytes": ("MaxJSONBytes", "REQUIRED"),
    "max-nesting-depth": ("MaxNestingDepth", "REQUIRED"),
    "max-identifier-length": ("MaxIdentifierLength", "REQUIRED"),
    "max-string-length-bytes": ("MaxStringLengthBytes", "REQUIRED"),
    "max-atom-count-per-property": ("MaxAtomCountPerProperty", "REQUIRED"),
    "max-frame-byte-count": ("MaxFrameByteCount", "REQUIRED"),
    "max-properties-per-stream": ("MaxPropertiesPerStream", "REQUIRED"),
    # Value-magnitude bound — enforced post-parse in the kernel (the Int64
    # wire range on rational components); mirrored for typed consumers.
    "max-rational-component-magnitude": ("MaxRationalComponentMagnitude", "REQUIRED"),
    # List-cardinality bounds — kernel-only; OPTIONAL for Go (header says
    # "mirrored verbatim" but per-list cap is enforced after JSON parsing,
    # so cgo-boundary rejection isn't beneficial).
    "max-messages-per-file": ("MaxMessagesPerFile", "REQUIRED"),
    "max-signals-per-message": ("MaxSignalsPerMessage", "REQUIRED"),
    "max-attributes-per-file": ("MaxAttributesPerFile", "REQUIRED"),
    "max-value-descriptions-per-file": ("MaxValueDescriptionsPerFile", "REQUIRED"),
    "max-comments-per-file": ("MaxCommentsPerFile", "OPTIONAL"),
    "max-nodes-per-file": ("MaxNodesPerFile", "OPTIONAL"),
    "max-value-tables-per-file": ("MaxValueTablesPerFile", "OPTIONAL"),
}


# Python mirror — kebab-case → SCREAMING_SNAKE.  Python mirrors a subset
# of the Go-mirrored constants today; the REQUIRED / OPTIONAL category is
# binding-independent (it's about whether the bound benefits from pre-FFI
# rejection on the input-side path).  Python's ctypes boundary has the
# same characteristic as Go's cgo boundary — every REQUIRED Agda constant
# should have a Python peer.
PYTHON_NAME_MAPPING: dict[str, tuple[str, str]] = {
    "max-dbc-text-bytes": ("MAX_DBC_TEXT_BYTES", "REQUIRED"),
    "max-json-bytes": ("MAX_JSON_BYTES", "REQUIRED"),
    "max-nesting-depth": ("MAX_NESTING_DEPTH", "REQUIRED"),
    "max-identifier-length": ("MAX_IDENTIFIER_LENGTH", "REQUIRED"),
    "max-string-length-bytes": ("MAX_STRING_LENGTH_BYTES", "REQUIRED"),
    "max-atom-count-per-property": ("MAX_ATOM_COUNT_PER_PROPERTY", "REQUIRED"),
    "max-frame-byte-count": ("MAX_FRAME_BYTE_COUNT", "REQUIRED"),
    "max-properties-per-stream": ("MAX_PROPERTIES_PER_STREAM", "REQUIRED"),
    "max-rational-component-magnitude": ("MAX_RATIONAL_COMPONENT_MAGNITUDE", "REQUIRED"),
    "max-messages-per-file": ("MAX_MESSAGES_PER_FILE", "REQUIRED"),
    "max-signals-per-message": ("MAX_SIGNALS_PER_MESSAGE", "REQUIRED"),
    "max-attributes-per-file": ("MAX_ATTRIBUTES_PER_FILE", "REQUIRED"),
    "max-value-descriptions-per-file": ("MAX_VALUE_DESCRIPTIONS_PER_FILE", "REQUIRED"),
    "max-comments-per-file": ("MAX_COMMENTS_PER_FILE", "OPTIONAL"),
    "max-nodes-per-file": ("MAX_NODES_PER_FILE", "OPTIONAL"),
    "max-value-tables-per-file": ("MAX_VALUE_TABLES_PER_FILE", "OPTIONAL"),
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
    "FrameByteCount": "BOUND_KIND_FRAME_BYTE_COUNT",
    "PropertyCount": "BOUND_KIND_PROPERTY_COUNT",
    "RationalComponentMagnitude": "BOUND_KIND_RATIONAL_COMPONENT_MAGNITUDE",
}

# C++ mirror: kebab-case to snake_case.  The header states it mirrors every
# numeric value verbatim and it carries the whole set, so every constant is
# REQUIRED: a mirror that drops one stops being the verbatim mirror it claims
# to be, whether or not the binding enforces that particular bound itself.
CPP_NAME_MAPPING: dict[str, tuple[str, str]] = {
    "max-dbc-text-bytes": ("max_dbc_text_bytes", "REQUIRED"),
    "max-json-bytes": ("max_json_bytes", "REQUIRED"),
    "max-nesting-depth": ("max_nesting_depth", "REQUIRED"),
    "max-identifier-length": ("max_identifier_length", "REQUIRED"),
    "max-string-length-bytes": ("max_string_length_bytes", "REQUIRED"),
    "max-atom-count-per-property": ("max_atom_count_per_property", "REQUIRED"),
    "max-frame-byte-count": ("max_frame_byte_count", "REQUIRED"),
    "max-properties-per-stream": ("max_properties_per_stream", "REQUIRED"),
    "max-rational-component-magnitude": ("max_rational_component_magnitude", "REQUIRED"),
    "max-messages-per-file": ("max_messages_per_file", "REQUIRED"),
    "max-signals-per-message": ("max_signals_per_message", "REQUIRED"),
    "max-attributes-per-file": ("max_attributes_per_file", "REQUIRED"),
    "max-value-descriptions-per-file": ("max_value_descriptions_per_file", "REQUIRED"),
    "max-comments-per-file": ("max_comments_per_file", "REQUIRED"),
    "max-nodes-per-file": ("max_nodes_per_file", "REQUIRED"),
    "max-value-tables-per-file": ("max_value_tables_per_file", "REQUIRED"),
}


# C++ BoundKind wire codes: `bound_kind_*` string views in the mirror header.
CPP_BOUND_KIND_MAPPING: dict[str, str] = {
    "InputLengthBytes": "bound_kind_input_length_bytes",
    "NestingDepth": "bound_kind_nesting_depth",
    "ArrayCardinality": "bound_kind_array_cardinality",
    "IdentifierLength": "bound_kind_identifier_length",
    "StringLength": "bound_kind_string_length",
    "AtomCount": "bound_kind_atom_count",
    "FrameByteCount": "bound_kind_frame_byte_count",
    "PropertyCount": "bound_kind_property_count",
    "RationalComponentMagnitude": "bound_kind_rational_component_magnitude",
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
    "FrameByteCount": "BoundKindFrameByteCount",
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
      * ``MAX_NAME: Final[int] = 64 * 1024 * 1024`` (typed) or
        ``MAX_NAME = 64 * 1024 * 1024`` (untyped) — both forms.
      * ``BOUND_KIND_NAME: Final[str] = "wire"`` lines.
    """
    max_pattern = re.compile(
        r"^\s*(?P<name>MAX_[A-Z][A-Z0-9_]*)\s*(?::\s*Final\[int\])?\s*=\s*"
        + r"(?P<expr>[^#\n]+?)\s*(?:#.*)?$",
        flags=re.MULTILINE,
    )
    constants: dict[str, int] = {}
    for m in max_pattern.finditer(text):
        value = _eval_int_expr(m.group("expr"))
        if value is not None:
            constants[m.group("name")] = value

    bk_pattern = re.compile(
        r"^\s*(?P<name>BOUND_KIND_[A-Z][A-Z0-9_]*)\s*(?::\s*Final\[str\])?\s*="
        + r'\s*"(?P<wire>[a-z_]+)"',
        flags=re.MULTILINE,
    )
    boundkind: dict[str, str] = {}
    for m in bk_pattern.finditer(text):
        boundkind[m.group("name")] = m.group("wire")

    return constants, boundkind


def _parse_cpp_limits(text: str) -> tuple[dict[str, int], dict[str, str]]:
    """Parse the C++ limits header, returning (max_* constants, bound_kind_* strings).

    Recognises ``inline constexpr std::uint64_t max_name = <expression>;`` and
    ``inline constexpr std::string_view bound_kind_name = "wire";``.  The wire
    pattern spans lines because a long code is wrapped onto the next one by the
    formatter.
    """
    max_pattern = re.compile(
        r"^inline constexpr std::uint64_t\s+(?P<name>max_[a-z0-9_]+)\s*=\s*(?P<expr>[^;]+);",
        flags=re.MULTILINE,
    )
    constants: dict[str, int] = {}
    for m in max_pattern.finditer(text):
        value = _eval_int_expr(m.group("expr"))
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
        + "list-cardinality enforced kernel-only)"
        for name, value in agda_consts.items()
        if name not in NAME_MAPPING
    )
    return diffs


def main() -> int:
    """Check Agda Limits SSOT parity against the Go, Python and C++ mirrors."""
    agda_consts, agda_boundkind = _parse_agda_limits(_read(AGDA_LIMITS))
    go_consts, go_boundkind = _parse_go_limits(_read(GO_LIMITS))
    py_consts, py_boundkind = _parse_python_limits(_read(PYTHON_LIMITS))
    cpp_consts, cpp_boundkind = _parse_cpp_limits(_read(CPP_LIMITS))

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
    # Agda-side drift: SSOT entries with no cross-check table mapping.
    diffs.extend(_check_agda_drift(agda_consts, agda_boundkind))

    if diffs:
        _ = sys.stderr.write("check-limits-parity: divergences detected\n\n")
        for d in diffs:
            _ = sys.stderr.write(f"  - {d}\n")
        mirrors = " / ".join(
            str(path.relative_to(REPO_ROOT)) for path in (GO_LIMITS, PYTHON_LIMITS, CPP_LIMITS)
        )
        _ = sys.stderr.write(
            f"\nfound {len(diffs)} divergence(s) between "
            + f"{AGDA_LIMITS.relative_to(REPO_ROOT)} (SSOT) and "
            + f"{mirrors} (mirrors).\n"
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
        + ": all in parity with Agda SSOT"
    )
    return 0


if __name__ == "__main__":
    sys.exit(main())
