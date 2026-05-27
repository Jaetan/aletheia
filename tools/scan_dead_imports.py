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

**Ignore file** — to suppress known false positives, this scanner loads
`tools/scan_dead_imports.ignore` (relative to repo root) if it exists.
The format is line-numberless so entries don't churn on every edit:

    # comment
    [Aletheia/Protocol/Routing.agda]
    if_then_else_
    _≤?_

    [Aletheia/Prelude.agda]
    map₁ to mapₑ

Each `[path]` section lists names to suppress in that file (path is
relative to `src/`).  Names are matched EXACTLY against the scanner's
reported text (including mixfix underscores and `X to Y` rename pairs).

Populate / refresh via `--write-ignore` after running the precise tool:
any name the precise tool kept but the scanner flags is a FP by
definition.

Usage:
    tools/scan_dead_imports.py [OPTIONS] [PATHS...]
    tools/scan_dead_imports.py --top 20 src/        # top-20 dirtiest files
    tools/scan_dead_imports.py --summary src/       # one-liners per file
    tools/scan_dead_imports.py src/Aletheia/X.agda  # detail for one file
    tools/scan_dead_imports.py --write-ignore       # capture current findings
                                                    # as a fresh ignore file
                                                    # (overwrites)

Options:
    --top N           Report only the top-N files by dead count.
    --summary         One-line summary per file, no per-name listing.
    --quiet           Only the totals line.
    --no-ignore       Don't load the ignore file (show raw findings).
    --write-ignore    Write current findings to `tools/scan_dead_imports.ignore`
                      and exit.  Use after the precise tool has verified the
                      codebase is dead-name-clean — remaining scanner findings
                      are by definition FPs.

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
from collections.abc import Iterable

IDENT_CHARS = r"A-Za-z0-9_'\-"

# Skip lines that re-export.  Their consumers depend on the re-exported
# names, so flagging a name as dead just because the file itself doesn't
# use it would produce a guaranteed FN — only the precise agda-driven tool
# can decide correctness here.
PUBLIC_RE = re.compile(r"\bpublic\b")


def _find_repo_root() -> Path:
    """Walk up looking for `aletheia.agda-lib`; fall back to script location."""
    for base in (Path.cwd().resolve(), Path(__file__).resolve()):
        for p in [base] + list(base.parents):
            if (p / "aletheia.agda-lib").exists():
                return p
    return Path(__file__).resolve().parent.parent


REPO_ROOT = _find_repo_root()
SRC_DIR = REPO_ROOT / "src"
IGNORE_PATH = REPO_ROOT / "tools" / "scan_dead_imports.ignore"


def load_ignore_file(path: Path) -> dict[str, set[str]]:
    """Parse an ignore file: returns {rel_path: set(names_to_suppress)}.

    Format:
        # comments allowed
        [Aletheia/Foo/Bar.agda]
        name1
        _≡_
        map₁ to mapₑ

        [Aletheia/Baz.agda]
        ...

    Names are stored verbatim and matched against scanner output exactly.
    Trailing whitespace stripped.  Empty sections (header followed by no
    names) are tolerated.  An entry with no preceding section header is
    silently dropped (with no warning, to keep the scanner quiet)."""
    ignore: dict[str, set[str]] = {}
    if not path.is_file():
        return ignore
    current: str | None = None
    for raw in path.read_text(encoding="utf-8").splitlines():
        line = raw.strip()
        if not line or line.startswith("#"):
            continue
        if line.startswith("[") and line.endswith("]"):
            current = line[1:-1].strip()
            ignore.setdefault(current, set())
        elif current is not None:
            ignore[current].add(line)
    return ignore


def write_ignore_file(
    path: Path,
    per_file: list[tuple[Path, list[tuple[int, str]]]],
    src_dir: Path,
) -> int:
    """Write the current findings as a fresh ignore file.

    Returns the number of (file, name) entries written.  Sorted alphabetically
    by file path; within a file, sorted alphabetically by name.  Removes
    duplicates within a file."""
    entries = 0
    with path.open("w", encoding="utf-8") as f:
        f.write("# tools/scan_dead_imports.ignore — known scanner false positives\n")
        f.write("#\n")
        f.write("# Populated by `tools/scan_dead_imports.py --write-ignore` AFTER\n")
        f.write("# a clean run of `tools/prune_unused_imports.py --include-public\n")
        f.write("# --final-check` confirms the codebase has no truly-removable\n")
        f.write("# dead imports.  Any name the precise agda-driven tool kept but\n")
        f.write("# this regex scanner flags is a false positive by definition,\n")
        f.write("# and belongs here.\n")
        f.write("#\n")
        f.write("# Hand-edit to add entries (e.g. a new mixfix operator the scanner\n")
        f.write("# misclassifies) or remove them when an entry becomes stale (the\n")
        f.write("# underlying name was genuinely deleted in a later edit).\n")
        f.write("#\n")
        f.write("# Format:\n")
        f.write("#   [path/relative/to/src.agda]\n")
        f.write("#     name1\n")
        f.write("#     _∷_\n")
        f.write("#     map₁ to mapₑ      ← renaming-pair from the scanner's output\n")
        f.write("#\n")
        f.write("# Names are matched EXACTLY against the scanner's reported text.\n")
        f.write("\n")
        sorted_files = sorted(per_file, key=lambda t: str(t[0]))
        for file_path, flagged in sorted_files:
            try:
                rel = str(file_path.relative_to(src_dir))
            except ValueError:
                rel = str(file_path)
            names = sorted(set(n for _, n in flagged))
            if not names:
                continue
            f.write(f"[{rel}]\n")
            for n in names:
                f.write(f"{n}\n")
                entries += 1
            f.write("\n")
    return entries


def _strip_comments(text: str) -> str:
    text = re.sub(r"\{-.*?-\}", "", text, flags=re.DOTALL)
    text = re.sub(r"--[^\n]*", "", text)
    return text


def _find_using_clauses(content: str) -> list[tuple[int, str]]:
    """Return list of (start_line_1indexed, names_blob) for every
    `using (...)` clause that is NOT on a `public` re-export line.

    Multi-line `using\n(...)` clauses are joined."""
    out: list[tuple[int, str]] = []
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


def _split_names(blob: str) -> list[str]:
    """Split a using-clause body on top-level `;` separators."""
    parts: list[str] = []
    depth = 0
    buf: list[str] = []
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


def scan_file(path: Path) -> list[tuple[int, str]]:
    """Return list of (line, name) for every flagged-dead candidate."""
    try:
        content = path.read_text(encoding="utf-8")
    except OSError:
        return []
    flagged: list[tuple[int, str]] = []
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
    parser.add_argument("--no-ignore", action="store_true", help="Don't load tools/scan_dead_imports.ignore (show raw findings)")
    parser.add_argument("--write-ignore", action="store_true", help="Write current findings to tools/scan_dead_imports.ignore and exit (overwrites)")
    args = parser.parse_args()

    paths = args.paths if args.paths else [SRC_DIR]
    files: list[Path] = []
    for p in paths:
        if p.is_file() and p.suffix == ".agda":
            files.append(p)
        elif p.is_dir():
            files.extend(sorted(p.rglob("*.agda")))
        else:
            print(f"warning: {p} not a file or directory", file=sys.stderr)

    # Scan first (without applying ignore — we need raw findings for
    # --write-ignore).
    per_file_raw: list[tuple[Path, list[tuple[int, str]]]] = []
    for f in files:
        flagged = scan_file(f)
        if flagged:
            per_file_raw.append((f, flagged))

    if args.write_ignore:
        IGNORE_PATH.parent.mkdir(parents=True, exist_ok=True)
        n = write_ignore_file(IGNORE_PATH, per_file_raw, SRC_DIR)
        print(
            f"wrote {n} entries across {len(per_file_raw)} files to {IGNORE_PATH}"
        )
        return 0

    # Apply ignore file (unless --no-ignore).
    if args.no_ignore:
        ignore_map: dict[str, set[str]] = {}
    else:
        ignore_map = load_ignore_file(IGNORE_PATH)

    per_file: list[tuple[Path, list[tuple[int, str]]]] = []
    suppressed_total = 0
    for f, flagged in per_file_raw:
        try:
            rel = str(f.relative_to(SRC_DIR))
        except ValueError:
            rel = str(f)
        sup = ignore_map.get(rel, set())
        kept = [(line, name) for (line, name) in flagged if name not in sup]
        suppressed_total += len(flagged) - len(kept)
        if kept:
            per_file.append((f, kept))

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
    if suppressed_total > 0:
        print(
            f"Total: {total} dead candidates across {flagged_files} flagged files "
            f"(of {len(files)} scanned; {suppressed_total} known-FP suppressed via "
            f"{IGNORE_PATH.name})"
        )
    else:
        print(
            f"Total: {total} dead candidates across {flagged_files} flagged files "
            f"(of {len(files)} scanned)"
        )
    return 0


if __name__ == "__main__":
    sys.exit(main())
