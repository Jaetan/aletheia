#!/usr/bin/env python3
"""tools/check_limits_parity.py — Enforce parity between Agda Limits SSOT and Go mirror.

Per AGENTS.md universal rule "Adversarial-input bounds at parser surfaces",
``src/Aletheia/Limits.agda`` is the single source of truth for every
adversarial-input bound enforced anywhere in the Aletheia stack.

The Go binding mirrors a subset of these constants at ``go/aletheia/limits.go``
for cgo-boundary pre-rejection (so pathological inputs are rejected before
being marshalled into a C buffer).  The mirror's header explicitly says
"Single source of truth: src/Aletheia/Limits.agda; numeric values are
mirrored here verbatim" — this script enforces that promise.

The Python and C++ bindings do NOT currently mirror these constants locally
(they observe the typed ``InputBoundExceeded`` error returned from the kernel)
— they are out of scope for this gate.

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


def main() -> int:
    agda_consts, agda_boundkind = _parse_agda_limits(_read(AGDA_LIMITS))
    go_consts, go_boundkind = _parse_go_limits(_read(GO_LIMITS))

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

    if diffs:
        sys.stderr.write("check-limits-parity: divergences detected\n\n")
        for d in diffs:
            sys.stderr.write(f"  - {d}\n")
        sys.stderr.write(
            f"\nfound {len(diffs)} divergence(s) between "
            f"{AGDA_LIMITS.relative_to(REPO_ROOT)} (SSOT) and "
            f"{GO_LIMITS.relative_to(REPO_ROOT)} (mirror).\n"
            "Reconcile either by updating the Go mirror, the Agda SSOT, "
            "or the NAME_MAPPING/BOUND_KIND_MAPPING tables in this script "
            "(when a new constant is intentionally added or removed).\n"
        )
        return 1

    print(
        f"check-limits-parity: {len(NAME_MAPPING)} numeric constants and "
        f"{len(BOUND_KIND_MAPPING)} BoundKind entries in parity between "
        "Agda SSOT and Go mirror"
    )
    return 0


if __name__ == "__main__":
    sys.exit(main())
