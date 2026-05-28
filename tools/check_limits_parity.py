#!/usr/bin/env python3
"""tools/check_limits_parity.py — Enforce parity between Agda Limits SSOT and binding mirrors.

Per AGENTS.md universal rule "Adversarial-input bounds at parser surfaces",
``src/Aletheia/Limits.agda`` is the single source of truth for every
adversarial-input bound enforced anywhere in the Aletheia stack.

Two language bindings mirror a subset of these constants for pre-FFI
rejection (so pathological inputs are rejected before being marshalled
across the language boundary):

* ``go/aletheia/limits.go`` — cgo-boundary mirror.
* ``python/aletheia/limits.py`` — ctypes-boundary mirror (the file IS
  a verbatim mirror per its header, so the same drift hazard applies as
  for the Go mirror; this gate covers both).

Each mirror's header explicitly says "Single source of truth:
src/Aletheia/Limits.agda; numeric values are mirrored here verbatim" —
this script enforces that promise on both sides.

The C++ binding does NOT mirror these constants locally; it consumes
the typed ``InputBoundExceeded`` error returned from the kernel.  Local
guards present in C++ (e.g. ``json_serialize.cpp`` depth cap) are
defense-in-depth using the kernel constant directly via
``aletheia::max_nesting_depth`` and do not form a separate mirror
surface.

Strategy:

1. Parse ``src/Aletheia/Limits.agda``:
   * Extract every ``boundKindCode <Tag> = "<wire-string>"`` mapping.
   * Extract every ``max-<kebab-name> : Nat`` / ``max-<kebab-name> = <number>``
     pair (numeric constants only; `Bool` constants if any are skipped).
2. Parse ``go/aletheia/limits.go``:
   * Extract every ``BoundKind<PascalTag> = "<wire-string>"`` mapping.
   * Extract every ``Max<PascalName> = <expression>`` const (evaluate the
     expression — `64 * 1024 * 1024`, `1024`, etc. — and compare).
3. Cross-check via a manual NAME_MAPPING table.  This avoids ambiguous
   kebab-case → PascalCase rules (e.g. ``DBC``, ``JSON`` stay uppercase).
4. Fail on any of: BoundKind wire-string mismatch, BoundKind missing from
   either side, numeric value mismatch on shared constants, or Agda
   constant marked REQUIRED but absent from Go.

Exit codes:
  0 — full parity between Agda SSOT and Go mirror.
  1 — at least one divergence detected.
  2 — usage error / file missing / parse failure.

Constants flagged OPTIONAL in NAME_MAPPING are list-cardinality bounds that
the Agda kernel enforces after JSON parsing; they don't benefit from
cgo-boundary pre-rejection, so omission from the Go mirror is acceptable.
REQUIRED constants are input-length / structural bounds where cgo-boundary
rejection is strictly preferable to letting a pathological buffer cross.

Forward-revert verified: changing ``MaxMessagesPerFile = 10000`` to ``9999``
in ``go/aletheia/limits.go`` fires this script; reverting returns to exit 0.
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

    Parses ``expr`` (with ``_`` digit separators stripped, as both Go and
    Python write ``1_000_000``) via ``ast.parse(..., mode="eval")`` and walks
    the tree through ``_eval_arith_node``'s whitelist.  Returns the integer
    result, or None when the expression fails to parse, contains a disallowed
    construct, or does not reduce to an ``int`` (e.g. a true-division result).
    The silent None return preserves the parsers' "skip lines that don't
    reduce to an integer constant" behaviour.  Shared by the Go and Python
    constant parsers, which both emit ``64 * 1024 * 1024`` for 64 MiB.
    """
    cleaned = expr.strip().replace("_", "")
    try:
        tree = ast.parse(cleaned, mode="eval")
        result = _eval_arith_node(tree.body)
    except (SyntaxError, ValueError, TypeError, ZeroDivisionError):
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
    mapping, the pre-rejection ``boundary`` and the ``header_path`` cited in
    REQUIRED-missing messages, leaving the parsed dicts as the only inputs.
    """

    label: str
    mapping: dict[str, tuple[str, str]]
    table_name: str
    binding: str
    boundary: str
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
    ``cfg.boundary`` names the pre-rejection boundary cited when REQUIRED.
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
                + f"(Agda has '{agda_name}={agda_val}'); marked REQUIRED — every "
                + f"REQUIRED bound must be pre-rejected at the {cfg.boundary} boundary, "
                + f"see {cfg.header_path} header"
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
    """Check Agda Limits SSOT parity against the Go and Python mirrors."""
    agda_consts, agda_boundkind = _parse_agda_limits(_read(AGDA_LIMITS))
    go_consts, go_boundkind = _parse_go_limits(_read(GO_LIMITS))
    py_consts, py_boundkind = _parse_python_limits(_read(PYTHON_LIMITS))

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
                boundary="cgo",
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
                boundary="ctypes",
                header_path="python/aletheia/limits.py",
            ),
            agda_consts,
            py_consts,
        )
    )
    # Agda-side drift: SSOT entries with no cross-check table mapping.
    diffs.extend(_check_agda_drift(agda_consts, agda_boundkind))

    if diffs:
        _ = sys.stderr.write("check-limits-parity: divergences detected\n\n")
        for d in diffs:
            _ = sys.stderr.write(f"  - {d}\n")
        _ = sys.stderr.write(
            f"\nfound {len(diffs)} divergence(s) between "
            + f"{AGDA_LIMITS.relative_to(REPO_ROOT)} (SSOT) and "
            + f"{GO_LIMITS.relative_to(REPO_ROOT)} / "
            + f"{PYTHON_LIMITS.relative_to(REPO_ROOT)} (mirrors).\n"
            + "Reconcile either by updating the Go / Python mirror, the Agda SSOT, "
            + "or the NAME_MAPPING / PYTHON_NAME_MAPPING / BOUND_KIND_MAPPING / "
            + "PYTHON_BOUND_KIND_MAPPING tables in this script "
            + "(when a new constant is intentionally added or removed).\n"
        )
        return 1

    emit(
        f"check-limits-parity: Go {len(NAME_MAPPING)} numeric + "
        + f"{len(BOUND_KIND_MAPPING)} BoundKind; "
        + f"Python {len(PYTHON_NAME_MAPPING)} numeric + "
        + f"{len(PYTHON_BOUND_KIND_MAPPING)} BoundKind — all in parity with Agda SSOT"
    )
    return 0


if __name__ == "__main__":
    sys.exit(main())
