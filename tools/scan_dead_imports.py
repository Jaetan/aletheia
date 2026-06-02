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
import bisect
import re
import sys
from pathlib import Path

from tools._common import emit, match_paren_content, split_top_level_semicolons

IDENT_CHARS = r"A-Za-z0-9_'\-"

# Shortest mixfix operator handled as `_X_` (two underscores + one inner char).
_MIN_MIXFIX_LEN = 3

# Skip lines that re-export.  Their consumers depend on the re-exported
# names, so flagging a name as dead just because the file itself doesn't
# use it would produce a guaranteed FN — only the precise agda-driven tool
# can decide correctness here.
PUBLIC_RE = re.compile(r"\bpublic\b")


def _find_repo_root() -> Path:
    """Walk up looking for ``aletheia.agda-lib``; fall back to script location."""
    for base in (Path.cwd().resolve(), Path(__file__).resolve()):
        for p in [base, *base.parents]:
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
    silently dropped (with no warning, to keep the scanner quiet).
    """
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
    duplicates within a file.
    """
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
            names = sorted({n for _, n in flagged})
            if not names:
                continue
            f.write(f"[{rel}]\n")
            for n in names:
                f.write(f"{n}\n")
                entries += 1
            f.write("\n")
    return entries


# Characters scanned after a `using (` while looking for a `public` keyword in
# the same block (a heuristic window — public re-exports are short).
_PUBLIC_LOOKAHEAD = 200


def _strip_comments(text: str) -> str:
    without_block = re.sub(r"\{-.*?-\}", "", text, flags=re.DOTALL)
    return re.sub(r"--[^\n]*", "", without_block)


def _enclosing_import_start(text: str, using_pos: int) -> int | None:
    """Return the offset of the import keyword enclosing the ``using`` at ``using_pos``.

    Walks backwards to the nearest ``import`` / ``open import``; returns None when
    the ``using`` is not inside an import statement (so the caller skips it).
    """
    before = text[:using_pos]
    last_import = max(before.rfind("\nimport "), before.rfind("\nopen import "))
    if last_import >= 0:
        return last_import
    # `open import` could be at the very start of the file (line 1).
    if before.startswith(("import ", "open import ")):
        return 0
    return None


def _find_using_clauses(content: str) -> list[tuple[int, str]]:
    """Find every ``using (...)`` clause that is not on a ``public`` re-export line.

    Returns a list of ``(start_line_1indexed, names_blob)``.  Multi-line clauses
    where the ``(`` follows ``using`` on the next line are joined.
    """
    out: list[tuple[int, str]] = []
    pat = re.compile(r"\busing\s*\(", flags=re.MULTILINE)
    text = _strip_comments(content)
    # Cumulative offset of each line start, for char-pos → 1-indexed line lookup.
    line_starts = [0]
    for i, ch in enumerate(text):
        if ch == "\n":
            line_starts.append(i + 1)

    for m in pat.finditer(text):
        last_import = _enclosing_import_start(text, m.start())
        if last_import is None:
            continue
        # Skip public re-export blocks (their uses are downstream only).
        if PUBLIC_RE.search(text[last_import : m.end() + _PUBLIC_LOOKAHEAD]):
            continue
        names_blob = match_paren_content(text, m.end())
        if names_blob is None:
            continue
        line = bisect.bisect_right(line_starts, m.start())
        out.append((line, names_blob))
    return out


def _split_names(blob: str) -> list[str]:
    """Split a using-clause body on top-level ``;`` separators."""
    return split_top_level_semicolons(blob)


def _count_body_refs(content: str, name: str) -> int:
    """Count standalone occurrences of `name` outside its declaration."""
    # Mixfix `_X_` — search for `X` (without underscores) not surrounded
    # by ident chars.  This catches infix `a X b` body uses but NOT
    # sections `(_X y)` (leading `_` defeats the lookbehind — known FN).
    if name.startswith("_") and name.endswith("_") and len(name) >= _MIN_MIXFIX_LEN:
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


FileFindings = tuple[Path, list[tuple[int, str]]]


def _build_arg_parser() -> argparse.ArgumentParser:
    """Construct the argument parser for the scan CLI."""
    parser = argparse.ArgumentParser(
        description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter
    )
    parser.add_argument(
        "paths", nargs="*", type=Path, help="Files or directories to scan (default: src/)"
    )
    parser.add_argument("--top", type=int, default=0, help="Report only the top-N dirtiest files")
    parser.add_argument("--summary", action="store_true", help="One-line summary per file")
    parser.add_argument("--quiet", action="store_true", help="Only print the totals line")
    parser.add_argument(
        "--no-ignore",
        action="store_true",
        help="Don't load tools/scan_dead_imports.ignore (show raw findings)",
    )
    parser.add_argument(
        "--write-ignore",
        action="store_true",
        help="Write current findings to tools/scan_dead_imports.ignore and exit (overwrites)",
    )
    return parser


def _gather_files(paths: list[Path]) -> list[Path]:
    """Collect .agda files from the given paths (directories scanned recursively)."""
    files: list[Path] = []
    for p in paths:
        if p.is_file() and p.suffix == ".agda":
            files.append(p)
        elif p.is_dir():
            files.extend(sorted(p.rglob("*.agda")))
        else:
            _ = sys.stderr.write(f"warning: {p} not a file or directory\n")
    return files


def _apply_ignore(
    per_file_raw: list[FileFindings], ignore_map: dict[str, set[str]]
) -> tuple[list[FileFindings], int]:
    """Drop ignored names from each file's findings; return (kept, suppressed_count)."""
    per_file: list[FileFindings] = []
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
    return per_file, suppressed_total


def _print_findings(per_file: list[FileFindings], *, summary: bool, top: int) -> None:
    """Print per-file findings, either as one-line summaries or grouped by line."""
    for f, flagged in per_file:
        if summary or top > 0:
            emit(f"  {len(flagged):3d}  {f}")
            continue
        emit(f"{f}  ({len(flagged)} dead candidates)")
        lines_grouped: dict[int, list[str]] = {}
        for line, name in flagged:
            lines_grouped.setdefault(line, []).append(name)
        for line in sorted(lines_grouped):
            names = lines_grouped[line]
            emit(f"  L{line}  ({len(names)} dead):")
            for n in names:
                emit(f"    {n}")


def _print_total(per_file: list[FileFindings], n_scanned: int, suppressed_total: int) -> None:
    """Print the trailing totals line, noting any ignore-file suppressions."""
    total = sum(len(f) for _, f in per_file)
    flagged_files = len(per_file)
    emit()
    suffix = (
        f"; {suppressed_total} known-FP suppressed via {IGNORE_PATH.name}"
        if suppressed_total > 0
        else ""
    )
    emit(
        f"Total: {total} dead candidates across {flagged_files} flagged files "
        + f"(of {n_scanned} scanned{suffix})"
    )


def main() -> int:
    """Scan the requested .agda files for dead-import candidates (always exits 0)."""
    args = _build_arg_parser().parse_args()

    paths = args.paths or [SRC_DIR]
    files = _gather_files(paths)

    # Scan first (without applying ignore — we need raw findings for --write-ignore).
    per_file_raw: list[FileFindings] = [(f, flagged) for f in files if (flagged := scan_file(f))]

    if args.write_ignore:
        IGNORE_PATH.parent.mkdir(parents=True, exist_ok=True)
        n = write_ignore_file(IGNORE_PATH, per_file_raw, SRC_DIR)
        emit(f"wrote {n} entries across {len(per_file_raw)} files to {IGNORE_PATH}")
        return 0

    ignore_map = {} if args.no_ignore else load_ignore_file(IGNORE_PATH)
    per_file, suppressed_total = _apply_ignore(per_file_raw, ignore_map)

    if args.top > 0:
        per_file.sort(key=lambda t: -len(t[1]))
        per_file = per_file[: args.top]

    if not args.quiet:
        _print_findings(per_file, summary=args.summary, top=args.top)
    _print_total(per_file, len(files), suppressed_total)
    return 0


if __name__ == "__main__":
    sys.exit(main())
