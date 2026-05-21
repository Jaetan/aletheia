#!/usr/bin/env python3
"""tools/scan_dead_imports.py — fast regex scanner for dead Agda imports.

This is the FAST tier of the dead-import workflow.  It uses regex pattern
matching to find candidate names in `using (...)` clauses that have no
body occurrences — much faster than the precise `agda`-driven verifier in
`tools/prune_unused_imports.py` (which can take 5-15 min per file).

It is NOT precise:
 - **False positives**: mixfix operators used via syntax sugar (e.g.
   `if cond then x else y` doesn't show the literal token `if_then_else_`),
   `_X_` mixfix sections `(_X y)` / `(x X_)`, `_X_` free combinators
   passed as higher-order arguments, `module X` qualified body access
   via `X.field` — these surface as flagged-dead but are LIVE.  See
   `memory/feedback_agda_import_pruning_safety.md` for the catalog.
 - **False negatives**: heavy `using (...)` clauses occasionally drop
   names from the regex match; `renaming (X to Y)` clauses are not
   processed.

Use this scanner for:
 - Pre-commit hooks (fast advisory check; SHOULD NOT block commits).
 - Quick local triage when you suspect a file has dead imports.

Use `tools/prune_unused_imports.py` instead when you want:
 - Precise, type-checker-validated removal.
 - Safe automatic application (`--include-public` and consumer-check).
 - CI-grade gates (exits 1 on findings).

Usage:
    tools/scan_dead_imports.py [OPTIONS] [PATHS...]
    tools/scan_dead_imports.py --top 20 src/        # top-20 dirtiest files
    tools/scan_dead_imports.py --summary src/       # one-liners per file
    tools/scan_dead_imports.py src/Aletheia/X.agda  # detail for one file

Options:
    --top N      Report only the top-N files by dead count.
    --summary    One-line summary per file, no per-name listing.
    --quiet      Only the totals line.

Exit:
    0 — always (warning-only; this tool never blocks workflows).

The `--check-only` semantic (exit 1 on findings) is intentionally NOT
implemented for this scanner: its false-positive rate is too high to
serve as a strict gate.  For a strict gate, use
`tools/prune_unused_imports.py --check-only`.
"""

from __future__ import annotations

import argparse
import os
import re
import sys
from pathlib import Path
from typing import Iterable, List, Tuple

IDENT_CHARS = r"A-Za-z0-9_'\-"

# Skip lines that re-export.  Their consumers depend on the re-exported
# names, so flagging a name as dead just because the file itself doesn't
# use it would produce a guaranteed FN — only the precise agda-driven tool
# can decide correctness here.
PUBLIC_RE = re.compile(r"\bpublic\b")


def _strip_comments(text: str) -> str:
    text = re.sub(r"\{-.*?-\}", "", text, flags=re.DOTALL)
    text = re.sub(r"--[^\n]*", "", text)
    return text


def _find_using_clauses(content: str) -> List[Tuple[int, str]]:
    """Return list of (start_line_1indexed, names_blob) for every
    `using (...)` clause that is NOT on a `public` re-export line.

    Multi-line `using\n(...)` clauses are joined."""
    out: List[Tuple[int, str]] = []
    pat = re.compile(r"\busing\s*\(", flags=re.MULTILINE)
    text = _strip_comments(content)
    # Get line offsets for converting char-pos to line-num.
    line_starts = [0]
    for i, ch in enumerate(text):
        if ch == "\n":
            line_starts.append(i + 1)

    def char_to_line(pos: int) -> int:
        # Binary search.
        lo, hi = 0, len(line_starts) - 1
        while lo < hi:
            mid = (lo + hi + 1) // 2
            if line_starts[mid] <= pos:
                lo = mid
            else:
                hi = mid - 1
        return lo + 1  # 1-indexed

    for m in pat.finditer(text):
        # Determine the import block this `using` belongs to.  Walk
        # backwards to find the enclosing `import ` / `open import `.
        before = text[: m.start()]
        last_import = max(before.rfind("\nimport "), before.rfind("\nopen import "))
        if last_import < 0:
            # `open import` could be at start of file (line 1).
            if before.startswith("import ") or before.startswith("open import "):
                last_import = 0
            else:
                continue
        # Skip if this block is a public re-export.
        block_tail = text[last_import : m.end() + 200]  # heuristic window
        if PUBLIC_RE.search(block_tail):
            continue
        # Extract the parenthesized content of this using(...).
        start = m.end()
        depth = 1
        i = start
        while i < len(text) and depth > 0:
            if text[i] == "(":
                depth += 1
            elif text[i] == ")":
                depth -= 1
                if depth == 0:
                    break
            i += 1
        if depth != 0:
            continue
        names_blob = text[start:i]
        line = char_to_line(m.start())
        out.append((line, names_blob))
    return out


def _split_names(blob: str) -> List[str]:
    """Split a using-clause body on top-level `;` separators."""
    parts: List[str] = []
    depth = 0
    buf: List[str] = []
    for ch in blob:
        if ch == "(":
            depth += 1
            buf.append(ch)
        elif ch == ")":
            depth -= 1
            buf.append(ch)
        elif ch == ";" and depth == 0:
            item = "".join(buf).strip()
            if item:
                parts.append(item)
            buf = []
        else:
            buf.append(ch)
    item = "".join(buf).strip()
    if item:
        parts.append(item)
    return parts


def _count_body_refs(content: str, name: str) -> int:
    """Count standalone occurrences of `name` outside its declaration."""
    # Mixfix `_X_` — search for `X` (without underscores) not surrounded
    # by ident chars.  This catches infix `a X b` body uses but NOT
    # sections `(_X y)` (leading `_` defeats the lookbehind — known FN).
    if name.startswith("_") and name.endswith("_") and len(name) >= 3:
        inner = name[1:-1]
        if not inner:
            return 0
        pat = re.compile(rf"(?<![{IDENT_CHARS}]){re.escape(inner)}(?![{IDENT_CHARS}])")
    elif name.startswith("module "):
        # `module X` — check for qualified-access `X.` in body.
        x = name[len("module ") :].strip()
        pat = re.compile(rf"{re.escape(x)}\.")
    else:
        pat = re.compile(rf"(?<![{IDENT_CHARS}]){re.escape(name)}(?![{IDENT_CHARS}])")
    return len(pat.findall(content))


def scan_file(path: Path) -> List[Tuple[int, str]]:
    """Return list of (line, name) for every flagged-dead candidate."""
    try:
        content = path.read_text(encoding="utf-8")
    except OSError:
        return []
    flagged: List[Tuple[int, str]] = []
    for line, blob in _find_using_clauses(content):
        for name in _split_names(blob):
            refs = _count_body_refs(content, name)
            # 1 ref = the import line itself.  0-1 refs = candidate dead.
            if refs <= 1:
                flagged.append((line, name))
    return flagged


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("paths", nargs="*", type=Path, help="Files or directories to scan (default: src/)")
    parser.add_argument("--top", type=int, default=0, help="Report only the top-N dirtiest files")
    parser.add_argument("--summary", action="store_true", help="One-line summary per file")
    parser.add_argument("--quiet", action="store_true", help="Only print the totals line")
    args = parser.parse_args()

    paths = args.paths if args.paths else [Path("src")]
    files: List[Path] = []
    for p in paths:
        if p.is_file() and p.suffix == ".agda":
            files.append(p)
        elif p.is_dir():
            files.extend(sorted(p.rglob("*.agda")))
        else:
            print(f"warning: {p} not a file or directory", file=sys.stderr)

    per_file: List[Tuple[Path, List[Tuple[int, str]]]] = []
    for f in files:
        flagged = scan_file(f)
        if flagged:
            per_file.append((f, flagged))

    if args.top > 0:
        per_file.sort(key=lambda t: -len(t[1]))
        per_file = per_file[: args.top]

    if not args.quiet:
        for f, flagged in per_file:
            if args.summary or args.top > 0:
                print(f"  {len(flagged):3d}  {f}")
            else:
                print(f"{f}  ({len(flagged)} dead candidates)")
                lines_grouped: dict = {}
                for line, name in flagged:
                    lines_grouped.setdefault(line, []).append(name)
                for line in sorted(lines_grouped):
                    names = lines_grouped[line]
                    print(f"  L{line}  ({len(names)} dead):")
                    for n in names:
                        print(f"    {n}")

    total = sum(len(f) for _, f in per_file)
    flagged_files = len(per_file)
    print()
    print(
        f"Total: {total} dead candidates across {flagged_files} flagged files "
        f"(of {len(files)} scanned)"
    )
    return 0


if __name__ == "__main__":
    sys.exit(main())
