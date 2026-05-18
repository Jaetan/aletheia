#!/usr/bin/env python3
"""tools/check_limits_parity.py — Enforce parity between Agda Limits SSOT and binding mirrors.

Per AGENTS.md universal rule "Adversarial-input bounds at parser surfaces",
``src/Aletheia/Limits.agda`` is the single source of truth for every
adversarial-input bound enforced anywhere in the Aletheia stack.

Two language bindings mirror a subset of these constants for pre-FFI
rejection (so pathological inputs are rejected before being marshalled
across the language boundary):

* ``go/aletheia/limits.go`` — cgo-boundary mirror.
* ``python/aletheia/limits.py`` — ctypes-boundary mirror (PY-S-22.1 R21:
  the file IS a verbatim mirror per its header, so the same drift
  hazard applies as for the Go mirror; this gate covers both).

Each mirror's header explicitly says "Single source of truth:
src/Aletheia/Limits.agda; numeric values are mirrored here verbatim" —
this script enforces that promise on both sides.

The C++ binding does NOT mirror these constants locally; it consumes
the typed ``InputBoundExceeded`` error returned from the kernel.  Local
guards present in C++ (e.g. ``json_serialize.cpp`` depth cap) are
defense-in-depth using the kernel constant directly via
``aletheia::max_nesting_depth`` (closed by R21 cluster 3) and do not
form a separate mirror surface.

Strategy:

1. Parse ``src/Aletheia/Limits.agda``:
   * Extract every ``boundKindCode <Tag> = "<wire-string>"`` mapping.
   * Extract every ``max-<kebab-name> : ℕ`` / ``max-<kebab-name> = <number>``
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

import re
import sys
from pathlib import Path

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
    "max-dbc-text-bytes":          ("MaxDBCTextBytes",          "REQUIRED"),
    "max-json-bytes":              ("MaxJSONBytes",             "REQUIRED"),
    "max-nesting-depth":           ("MaxNestingDepth",          "REQUIRED"),
    "max-identifier-length":       ("MaxIdentifierLength",      "REQUIRED"),
    "max-string-length-bytes":     ("MaxStringLengthBytes",     "REQUIRED"),
    "max-atom-count-per-property": ("MaxAtomCountPerProperty",  "REQUIRED"),
    "max-frame-byte-count":        ("MaxFrameByteCount",        "REQUIRED"),
    # List-cardinality bounds — kernel-only; OPTIONAL for Go (header says
    # "mirrored verbatim" but per-list cap is enforced after JSON parsing,
    # so cgo-boundary rejection isn't beneficial).
    "max-messages-per-file":           ("MaxMessagesPerFile",           "REQUIRED"),
    "max-signals-per-message":         ("MaxSignalsPerMessage",         "REQUIRED"),
    "max-attributes-per-file":         ("MaxAttributesPerFile",         "REQUIRED"),
    "max-value-descriptions-per-file": ("MaxValueDescriptionsPerFile",  "REQUIRED"),
    "max-comments-per-file":           ("MaxCommentsPerFile",           "OPTIONAL"),
    "max-nodes-per-file":              ("MaxNodesPerFile",              "OPTIONAL"),
    "max-value-tables-per-file":       ("MaxValueTablesPerFile",        "OPTIONAL"),
}


# Python mirror — kebab-case → SCREAMING_SNAKE.  PY-S-22.1 (R21) closure:
# Python mirrors a subset of the Go-mirrored constants today; the
# REQUIRED / OPTIONAL category is binding-independent (it's about whether
# the bound benefits from pre-FFI rejection on the input-side path).
# Python's ctypes boundary has the same characteristic as Go's cgo
# boundary — every REQUIRED Agda constant should have a Python peer.
PYTHON_NAME_MAPPING: dict[str, tuple[str, str]] = {
    "max-dbc-text-bytes":              ("MAX_DBC_TEXT_BYTES",              "REQUIRED"),
    "max-json-bytes":                  ("MAX_JSON_BYTES",                  "REQUIRED"),
    "max-nesting-depth":               ("MAX_NESTING_DEPTH",               "REQUIRED"),
    "max-identifier-length":           ("MAX_IDENTIFIER_LENGTH",           "REQUIRED"),
    "max-string-length-bytes":         ("MAX_STRING_LENGTH_BYTES",         "REQUIRED"),
    "max-atom-count-per-property":     ("MAX_ATOM_COUNT_PER_PROPERTY",     "REQUIRED"),
    "max-frame-byte-count":            ("MAX_FRAME_BYTE_COUNT",            "REQUIRED"),
    "max-messages-per-file":           ("MAX_MESSAGES_PER_FILE",           "REQUIRED"),
    "max-signals-per-message":         ("MAX_SIGNALS_PER_MESSAGE",         "REQUIRED"),
    "max-attributes-per-file":         ("MAX_ATTRIBUTES_PER_FILE",         "REQUIRED"),
    "max-value-descriptions-per-file": ("MAX_VALUE_DESCRIPTIONS_PER_FILE", "REQUIRED"),
    "max-comments-per-file":           ("MAX_COMMENTS_PER_FILE",           "OPTIONAL"),
    "max-nodes-per-file":              ("MAX_NODES_PER_FILE",              "OPTIONAL"),
    "max-value-tables-per-file":       ("MAX_VALUE_TABLES_PER_FILE",       "OPTIONAL"),
}


# Python BoundKind enum: every entry's wire-code string must match between
# Agda and Python (`BOUND_KIND_*` consts in `python/aletheia/limits.py`).
PYTHON_BOUND_KIND_MAPPING: dict[str, str] = {
    "InputLengthBytes":  "BOUND_KIND_INPUT_LENGTH_BYTES",
    "NestingDepth":      "BOUND_KIND_NESTING_DEPTH",
    "ArrayCardinality":  "BOUND_KIND_ARRAY_CARDINALITY",
    "IdentifierLength":  "BOUND_KIND_IDENTIFIER_LENGTH",
    "StringLength":      "BOUND_KIND_STRING_LENGTH",
    "AtomCount":         "BOUND_KIND_ATOM_COUNT",
    "FrameByteCount":    "BOUND_KIND_FRAME_BYTE_COUNT",
}

# BoundKind enum: every entry's wire-code string must match between Agda
# (`boundKindCode`) and Go (`BoundKind*` consts).  Mapping below pairs the
# Agda ADT tag with the Go const name.
BOUND_KIND_MAPPING: dict[str, str] = {
    "InputLengthBytes":  "BoundKindInputLengthBytes",
    "NestingDepth":      "BoundKindNestingDepth",
    "ArrayCardinality":  "BoundKindArrayCardinality",
    "IdentifierLength":  "BoundKindIdentifierLength",
    "StringLength":      "BoundKindStringLength",
    "AtomCount":         "BoundKindAtomCount",
    "FrameByteCount":    "BoundKindFrameByteCount",
}


def _read(path: Path) -> str:
    if not path.is_file():
        sys.stderr.write(f"check-limits-parity: {path} not found\n")
        sys.exit(2)
    return path.read_text(encoding="utf-8")


def _parse_agda_limits(text: str) -> tuple[dict[str, int], dict[str, str]]:
    """Parse Agda Limits.agda — returns (max-constants, boundKindCode-table).

    Constants are parsed from the ``name : ℕ\\nname = <number>`` pattern.
    Only numeric literal RHS values are extracted (no arithmetic — Agda
    Limits.agda intentionally uses literal values for readability).
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


def _eval_go_expr(expr: str) -> int | None:
    """Evaluate a Go integer expression — integer literals, ``*`` products,
    and underscored separators only.  Returns None on parse failure.
    """
    s = expr.strip().replace("_", "")
    # Accept patterns: ``\d+`` or ``\d+\s*\*\s*\d+(\s*\*\s*\d+)*``.
    if not re.fullmatch(r"\d+(\s*\*\s*\d+)*", s):
        return None
    try:
        return eval(s, {"__builtins__": {}}, {})  # noqa: S307 — input is regex-validated.
    except (SyntaxError, ValueError):
        return None


def _parse_go_limits(text: str) -> tuple[dict[str, int], dict[str, str]]:
    """Parse Go limits.go const blocks — returns (Max* constants, BoundKind* strings).

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
        value = _eval_go_expr(m.group("expr"))
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


def _eval_python_expr(expr: str) -> int | None:
    """Evaluate a Python integer expression — literals, ``*`` products,
    and underscored separators only.  Identical accept-set to the Go
    evaluator; Python and Go both write `64 * 1024 * 1024` for 64 MiB.
    """
    s = expr.strip().replace("_", "")
    if not re.fullmatch(r"\d+(\s*\*\s*\d+)*", s):
        return None
    try:
        return eval(s, {"__builtins__": {}}, {})  # noqa: S307 — input is regex-validated.
    except (SyntaxError, ValueError):
        return None


def _parse_python_limits(text: str) -> tuple[dict[str, int], dict[str, str]]:
    """Parse Python limits.py — returns (MAX_* constants, BOUND_KIND_* strings).

    Recognises:
      * ``MAX_NAME: Final[int] = 64 * 1024 * 1024`` (typed) or
        ``MAX_NAME = 64 * 1024 * 1024`` (untyped) — both forms.
      * ``BOUND_KIND_NAME: Final[str] = "wire"`` lines.
    """
    max_pattern = re.compile(
        r"^\s*(?P<name>MAX_[A-Z][A-Z0-9_]*)\s*(?::\s*Final\[int\])?\s*=\s*(?P<expr>[^#\n]+?)\s*(?:#.*)?$",
        flags=re.MULTILINE,
    )
    constants: dict[str, int] = {}
    for m in max_pattern.finditer(text):
        value = _eval_python_expr(m.group("expr"))
        if value is not None:
            constants[m.group("name")] = value

    bk_pattern = re.compile(
        r"^\s*(?P<name>BOUND_KIND_[A-Z][A-Z0-9_]*)\s*(?::\s*Final\[str\])?\s*=\s*\"(?P<wire>[a-z_]+)\"",
        flags=re.MULTILINE,
    )
    boundkind: dict[str, str] = {}
    for m in bk_pattern.finditer(text):
        boundkind[m.group("name")] = m.group("wire")

    return constants, boundkind


def main() -> int:
    agda_consts, agda_boundkind = _parse_agda_limits(_read(AGDA_LIMITS))
    go_consts, go_boundkind = _parse_go_limits(_read(GO_LIMITS))
    py_consts, py_boundkind = _parse_python_limits(_read(PYTHON_LIMITS))

    if not agda_consts:
        sys.stderr.write("check-limits-parity: no max-* constants parsed from Limits.agda\n")
        return 2
    if not agda_boundkind:
        sys.stderr.write("check-limits-parity: no boundKindCode entries parsed from Limits.agda\n")
        return 2

    diffs: list[str] = []

    # 1) BoundKind wire-code parity.  Required on both sides.
    for agda_tag, go_name in BOUND_KIND_MAPPING.items():
        agda_wire = agda_boundkind.get(agda_tag)
        go_wire = go_boundkind.get(go_name)
        if agda_wire is None:
            diffs.append(f"BoundKind: Agda missing entry for tag '{agda_tag}'")
            continue
        if go_wire is None:
            diffs.append(f"BoundKind: Go missing entry for const '{go_name}'")
            continue
        if agda_wire != go_wire:
            diffs.append(
                f"BoundKind {agda_tag} / {go_name}: wire mismatch — "
                f"Agda='{agda_wire}' vs Go='{go_wire}'"
            )

    # Detect Agda boundKindCode entries not represented in the mapping.
    for tag in agda_boundkind:
        if tag not in BOUND_KIND_MAPPING:
            diffs.append(
                f"BoundKind: Agda has tag '{tag}' (wire='{agda_boundkind[tag]}') "
                f"but BOUND_KIND_MAPPING in check_limits_parity.py has no entry — "
                "add it"
            )

    # Detect Go BoundKind constants not represented in the mapping.
    mapped_go_bk = set(BOUND_KIND_MAPPING.values())
    for go_name in go_boundkind:
        if go_name not in mapped_go_bk:
            diffs.append(
                f"BoundKind: Go has const '{go_name}' (wire='{go_boundkind[go_name]}') "
                f"but BOUND_KIND_MAPPING in check_limits_parity.py has no entry — "
                "this is a Go-side const without an Agda peer; either add the Agda "
                "entry or remove the Go const"
            )

    # 2) Numeric constant parity.
    for agda_name, (go_name, category) in NAME_MAPPING.items():
        agda_val = agda_consts.get(agda_name)
        go_val = go_consts.get(go_name)
        if agda_val is None:
            diffs.append(f"max-constant: Agda missing '{agda_name}'")
            continue
        if go_val is None and category == "REQUIRED":
            diffs.append(
                f"max-constant: Go missing '{go_name}' (Agda has '{agda_name}={agda_val}'); "
                "marked REQUIRED — every REQUIRED bound must be pre-rejected at the cgo "
                "boundary, see go/aletheia/limits.go header"
            )
            continue
        if go_val is not None and agda_val != go_val:
            diffs.append(
                f"max-constant {agda_name} / {go_name}: value mismatch — "
                f"Agda={agda_val} vs Go={go_val}"
            )

    # Detect Agda max-* constants not represented in NAME_MAPPING (drift on Agda side).
    for name in agda_consts:
        if name not in NAME_MAPPING:
            diffs.append(
                f"max-constant: Agda has '{name}={agda_consts[name]}' but "
                "NAME_MAPPING in check_limits_parity.py has no entry — "
                "add it (REQUIRED if input-size / structural, OPTIONAL if "
                "list-cardinality enforced kernel-only)"
            )

    # Detect Go Max* constants not represented in NAME_MAPPING (stale Go mirror).
    mapped_go = {v[0] for v in NAME_MAPPING.values()}
    for name in go_consts:
        if name not in mapped_go:
            diffs.append(
                f"max-constant: Go has '{name}={go_consts[name]}' but "
                "NAME_MAPPING in check_limits_parity.py has no entry — "
                "this is a Go-side const without an Agda peer; either add "
                "the Agda entry (SSOT first) or remove the Go const"
            )

    # 3) Python BoundKind wire-code parity.
    for agda_tag, py_name in PYTHON_BOUND_KIND_MAPPING.items():
        agda_wire = agda_boundkind.get(agda_tag)
        py_wire = py_boundkind.get(py_name)
        if agda_wire is None:
            diffs.append(f"Python BoundKind: Agda missing entry for tag '{agda_tag}'")
            continue
        if py_wire is None:
            diffs.append(f"Python BoundKind: Python missing entry for const '{py_name}'")
            continue
        if agda_wire != py_wire:
            diffs.append(
                f"Python BoundKind {agda_tag} / {py_name}: wire mismatch — "
                f"Agda='{agda_wire}' vs Python='{py_wire}'"
            )

    # Detect Python BoundKind constants not represented in the mapping
    # (stale Python mirror).
    mapped_py_bk = set(PYTHON_BOUND_KIND_MAPPING.values())
    for py_name in py_boundkind:
        if py_name not in mapped_py_bk:
            diffs.append(
                f"Python BoundKind: Python has const '{py_name}' (wire='{py_boundkind[py_name]}') "
                f"but PYTHON_BOUND_KIND_MAPPING in check_limits_parity.py has no entry — "
                "this is a Python-side const without an Agda peer; either add the Agda "
                "entry or remove the Python const"
            )

    # 4) Python numeric constant parity.
    for agda_name, (py_name, category) in PYTHON_NAME_MAPPING.items():
        agda_val = agda_consts.get(agda_name)
        py_val = py_consts.get(py_name)
        if agda_val is None:
            diffs.append(f"Python max-constant: Agda missing '{agda_name}'")
            continue
        if py_val is None and category == "REQUIRED":
            diffs.append(
                f"Python max-constant: Python missing '{py_name}' (Agda has '{agda_name}={agda_val}'); "
                "marked REQUIRED — every REQUIRED bound must be pre-rejected at the ctypes "
                "boundary, see python/aletheia/limits.py header"
            )
            continue
        if py_val is not None and agda_val != py_val:
            diffs.append(
                f"Python max-constant {agda_name} / {py_name}: value mismatch — "
                f"Agda={agda_val} vs Python={py_val}"
            )

    # Detect Python MAX_* constants not represented in PYTHON_NAME_MAPPING.
    mapped_py = {v[0] for v in PYTHON_NAME_MAPPING.values()}
    for name in py_consts:
        if name not in mapped_py:
            diffs.append(
                f"Python max-constant: Python has '{name}={py_consts[name]}' but "
                "PYTHON_NAME_MAPPING in check_limits_parity.py has no entry — "
                "this is a Python-side const without an Agda peer; either add "
                "the Agda entry (SSOT first) or remove the Python const"
            )

    if diffs:
        sys.stderr.write("check-limits-parity: divergences detected\n\n")
        for d in diffs:
            sys.stderr.write(f"  - {d}\n")
        sys.stderr.write(
            f"\nfound {len(diffs)} divergence(s) between "
            f"{AGDA_LIMITS.relative_to(REPO_ROOT)} (SSOT) and "
            f"{GO_LIMITS.relative_to(REPO_ROOT)} / "
            f"{PYTHON_LIMITS.relative_to(REPO_ROOT)} (mirrors).\n"
            "Reconcile either by updating the Go / Python mirror, the Agda SSOT, "
            "or the NAME_MAPPING / PYTHON_NAME_MAPPING / BOUND_KIND_MAPPING / "
            "PYTHON_BOUND_KIND_MAPPING tables in this script "
            "(when a new constant is intentionally added or removed).\n"
        )
        return 1

    print(
        f"check-limits-parity: Go {len(NAME_MAPPING)} numeric + "
        f"{len(BOUND_KIND_MAPPING)} BoundKind; "
        f"Python {len(PYTHON_NAME_MAPPING)} numeric + "
        f"{len(PYTHON_BOUND_KIND_MAPPING)} BoundKind — all in parity with Agda SSOT"
    )
    return 0


if __name__ == "__main__":
    sys.exit(main())
