# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
"""tools/check_bound_enforcement.py — every BoundKind ctor must have at least one emit site.

AGENTS.md universal rule "Adversarial-input bounds at parser surfaces"
requires every adversarial bound to be rejected as a typed
``Error.InputBoundExceeded <BoundKind> observed limit``.  The
``BoundKind`` ADT in ``src/Aletheia/Limits.agda`` enumerates the supported
kinds; each ctor must appear in at least one ``InputBoundExceeded <Ctor>``
emit site under ``src/``.  A ctor declared but never emitted is dead
metadata — the wire code is unreachable and the bound goes unenforced.

Strategy:

1. Parse the ``data BoundKind : Set where`` block in ``Limits.agda`` for
   the list of constructor names.
2. Walk every ``.agda`` file under ``src/`` (excluding ``Limits.agda``
   and ``Error.agda``, which only declare / dispatch on ``BoundKind``)
   and count occurrences of ``InputBoundExceeded <Ctor>`` per ctor.
3. Fail with a per-ctor coverage report if any ctor has zero matches.

Exit codes:
  0 — every BoundKind ctor has at least one emit site.
  1 — at least one ctor has zero emit sites.
  2 — parse / I/O error.
"""

from __future__ import annotations

import re
import sys
from pathlib import Path

from tools._common import emit

REPO_ROOT = Path(__file__).resolve().parent.parent
LIMITS_PATH = REPO_ROOT / "src" / "Aletheia" / "Limits.agda"
SRC_ROOT = REPO_ROOT / "src"

# Modules excluded from emit-site scanning:
#   * Limits.agda declares the BoundKind ADT.
#   * Error.agda dispatches in formatError / errorCode / errorExtras on
#     `InputBoundExceeded kind obs limit`, with `kind` as a variable —
#     not a literal ctor.  Including it would over-count.
EXCLUDED_FILES = {
    REPO_ROOT / "src" / "Aletheia" / "Limits.agda",
    REPO_ROOT / "src" / "Aletheia" / "Error.agda",
    REPO_ROOT / "src" / "Aletheia" / "Protocol" / "ResponseFormat.agda",
}


def _parse_boundkind_ctors(limits_path: Path) -> list[str]:
    """Return the list of ctor names declared in BoundKind.

    The expected shape:
        data BoundKind : Set where
          -- comment
          InputLengthBytes        : BoundKind
          NestingDepth            : BoundKind
          ...
    """
    if not limits_path.is_file():
        sys.stderr.write(f"check-bound-enforcement: {limits_path} not found\n")
        sys.exit(2)
    text = limits_path.read_text(encoding="utf-8")
    decl_re = re.compile(
        r"^data\s+BoundKind\s*:\s*Set\s+where\s*$",
        re.MULTILINE,
    )
    match = decl_re.search(text)
    if not match:
        sys.stderr.write(
            "check-bound-enforcement: could not locate "
            + f"`data BoundKind : Set where` in {limits_path}\n"
        )
        sys.exit(2)
    # Walk subsequent lines.  A ctor line looks like:
    #     <Name>{whitespace}: BoundKind
    # The block ends at the first non-indented, non-comment, non-ctor line
    # (e.g., the `boundKindCode` definition).
    ctor_line_re = re.compile(r"^\s+([A-Z][A-Za-z0-9_-]*)\s*:\s*BoundKind\s*$")
    ctors: list[str] = []
    for line in text[match.end() :].splitlines():
        if not line.strip():
            continue
        if line.lstrip().startswith("--"):
            continue
        m = ctor_line_re.match(line)
        if m:
            ctors.append(m.group(1))
            continue
        # First non-blank, non-comment, non-ctor line ends the block.
        break
    if not ctors:
        sys.stderr.write(f"check-bound-enforcement: no BoundKind ctors parsed from {limits_path}\n")
        sys.exit(2)
    return ctors


def _count_emit_sites(ctor: str, files: list[Path]) -> dict[Path, int]:
    r"""For one ctor, return a dict of file → emit-site count.

    An emit site is the regex ``\bInputBoundExceeded\s+<Ctor>\b``.
    Comments are not stripped — a commented-out emit site would have the
    same shape and should be flagged either way (a commented-out emit
    site is not an emit site).
    """
    # Note: we DO scan comments.  A commented emit site is not enforcement.
    # The simplest interpretation: only line-start `--` stripping would catch
    # block-comment edge cases; better to require the actual code-level emit.
    pat = re.compile(rf"\bInputBoundExceeded\s+{re.escape(ctor)}\b")
    hits: dict[Path, int] = {}
    for f in files:
        text = f.read_text(encoding="utf-8")
        # Strip Agda line comments to avoid false positives.
        stripped = re.sub(r"--[^\n]*", "", text)
        count = len(pat.findall(stripped))
        if count > 0:
            hits[f] = count
    return hits


def _agda_files(root: Path, exclude: set[Path]) -> list[Path]:
    return sorted(
        p for p in root.rglob("*.agda") if p.resolve() not in {e.resolve() for e in exclude}
    )


def main() -> int:
    """Verify every BoundKind ctor has at least one InputBoundExceeded emit site."""
    ctors = _parse_boundkind_ctors(LIMITS_PATH)
    files = _agda_files(SRC_ROOT, EXCLUDED_FILES)
    if not files:
        sys.stderr.write(f"check-bound-enforcement: no .agda files under {SRC_ROOT}\n")
        return 2
    missing: list[str] = []
    per_ctor_counts: dict[str, int] = {}
    for ctor in ctors:
        hits = _count_emit_sites(ctor, files)
        total = sum(hits.values())
        per_ctor_counts[ctor] = total
        if total == 0:
            missing.append(ctor)
    if missing:
        sys.stderr.write(
            "check-bound-enforcement: BoundKind ctors with zero "
            + "`InputBoundExceeded <Ctor>` emit sites:\n"
        )
        for c in missing:
            sys.stderr.write(f"  - {c}\n")
        sys.stderr.write(
            "\nEvery ctor in `data BoundKind` must be emitted at least once at a parser\n"
            + 'or handler boundary.  AGENTS.md universal rule "Adversarial-input bounds\n'
            + 'at parser surfaces" requires typed `Error.InputBoundExceeded` rejection;\n'
            + "a ctor with no emit site has an unreachable wire code.\n"
        )
        return 1
    summary_pairs = ", ".join(f"{c}={per_ctor_counts[c]}" for c in ctors)
    emit(f"check-bound-enforcement: all {len(ctors)} BoundKind ctors emitted ({summary_pairs})")
    return 0


if __name__ == "__main__":
    sys.exit(main())
