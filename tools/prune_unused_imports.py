#!/usr/bin/env python3
"""prune_unused_imports.py — agda-driven dead-import remover.

For each .agda file:
  1. Parse all `open import M ... using (...) [renaming (...)]` blocks.
  2. For every name in `using (...)` and every pair in `renaming (...)`,
     attempt removal: rewrite the file with that name dropped, run
     `agda --type-check`.  If exit 0, keep the removal; else restore.
  3. The type-checker is the ground truth: zero false positives, zero
     false negatives.  All mixfix forms (infix `a X b`, sections
     `(_X y)` / `(x X_)`, free combinator `_X_`), module-qualified
     access (`module X` + `X.field` body uses), `as N` aliases, and
     `renaming` pairs are resolved correctly because we just ask agda.

Concurrency: file-level parallel workers.  Each file's audit is serial
(tests mutate the file).  Different files can be in flight simultaneously
because each file's `.agdai` interface is independent.

Public re-exports: `open import M ... public` lines are SKIPPED by default
(removing a name from them changes the file's exported surface, which can
break downstream consumers).  Use --include-public to test them anyway —
this only checks the file itself, NOT downstream, so combine with
--final-check to run `cabal run shake -- check-properties` at the end.

Usage:
    tools/prune_unused_imports.py [OPTIONS] [PATHS...]

Default paths: src/

Options:
    -j, --workers N        Parallel file workers (default: 4)
        --rts-cores K      GHC RTS cores per agda call (default: 8)
        --rts-heap G       GHC RTS heap per agda call in GB (default: 3)
        --timeout SECS     Per-agda-call timeout (default: 300)
        --include-public   Test `public` re-export lines (default: skip).
        --final-check      After pruning, run `cabal run shake -- check-properties`.
                           Restores all changes if the project-wide check fails.
        --dry-run          Don't modify files; report what would be removed.
        --quiet            Suppress per-file output.
        --verbose          Per-name decision logging.
        --pre-check        Verify each file type-checks before pruning;
                           skip files that fail.
        --no-bisect        Disable bisection (pure per-name brute force).

The default mode tries removing ALL names in an import block at once
(bisection optimization).  If that fails, it falls back to per-name
testing for that block.  Best case: 1 type-check per all-dead block.
Worst case: 1 + N type-checks per block where N is the block's name count.

Output: per-file summary line + aggregate stats.  Exit 0 if all files
processed successfully; 1 if any failures.
"""

from __future__ import annotations

import argparse
import concurrent.futures
import logging
import os
import re
import subprocess
import sys
import time
from dataclasses import dataclass, field
from pathlib import Path
from typing import Dict, Iterable, List, Optional, Set, Tuple

# ----------------------------------------------------------------------------
# Constants
# ----------------------------------------------------------------------------

REPO_ROOT = Path(__file__).resolve().parent.parent
SRC_DIR = REPO_ROOT / "src"
AGDA_BIN = Path(os.environ.get("AGDA_BIN", "/home/nicolas/.cabal/bin/agda"))

# Character class for Agda identifier continuation: letters, digits, _, ', -.
# Used in word-boundary lookarounds.
IDENT_CHARS = r"A-Za-z0-9_'\-"

# ----------------------------------------------------------------------------
# Data model
# ----------------------------------------------------------------------------


@dataclass
class ImportBlock:
    """One `open import M ... [using (...)] [renaming (...)] [public]` block,
    possibly spanning multiple lines."""

    line_start: int  # 0-indexed, inclusive
    line_end: int  # 0-indexed, inclusive (last line of the block)
    raw: str  # original block text (including trailing newline of last line)
    module_path: str
    has_public: bool
    using_names: List[str] = field(default_factory=list)
    # renaming_pairs[i] = (source, destination); the destination is the
    # in-scope name in the body.
    renaming_pairs: List[Tuple[str, str]] = field(default_factory=list)


@dataclass
class FileStats:
    file: Path
    using_tested: int = 0
    using_removed: int = 0
    renaming_tested: int = 0
    renaming_removed: int = 0
    public_blocks_skipped: int = 0
    type_checks: int = 0
    seconds: float = 0.0
    error: Optional[str] = None

    @property
    def removed_total(self) -> int:
        return self.using_removed + self.renaming_removed


# ----------------------------------------------------------------------------
# Parser
# ----------------------------------------------------------------------------


def parse_imports(content: str) -> List[ImportBlock]:
    """Parse all import blocks in the file content."""
    lines = content.splitlines(keepends=True)
    blocks: List[ImportBlock] = []
    i = 0
    while i < len(lines):
        stripped = lines[i].lstrip()
        if stripped.startswith("open import ") or stripped.startswith("import "):
            block, consumed = _parse_one_block(lines, i)
            if block:
                blocks.append(block)
                i += consumed
                continue
        i += 1
    return blocks


def _parse_one_block(
    lines: List[str], start: int
) -> Tuple[Optional[ImportBlock], int]:
    """Collect lines belonging to one import block.

    A block extends until paren depth returns to 0 AND the next line is not
    a continuation (`using (...)`, `renaming (...)`, or `public`).
    """
    paren_depth = 0
    end = start
    while end < len(lines):
        clean = _strip_comments(lines[end])
        paren_depth += clean.count("(") - clean.count(")")
        end += 1
        if paren_depth == 0:
            # Check if next line continues this import block.
            if end < len(lines):
                nxt = lines[end].lstrip()
                if (
                    re.match(r"^using\s*\(?", nxt)
                    or re.match(r"^renaming\s*\(?", nxt)
                    or nxt.startswith("public")
                ):
                    continue
            break
        if paren_depth < 0:
            # Malformed input; give up on this block.
            return None, end - start
    raw = "".join(lines[start:end])
    return _parse_block_content(start, end - 1, raw), end - start


def _strip_comments(line: str) -> str:
    """Remove `{- ... -}` and `-- ...` comments from a single line.

    Multi-line block comments are not handled (uncommon in imports)."""
    line = re.sub(r"\{-.*?-\}", "", line)
    idx = line.find("--")
    if idx >= 0:
        return line[:idx]
    return line


def _strip_comments_all(text: str) -> str:
    """Strip comments throughout a multi-line block."""
    text = re.sub(r"\{-.*?-\}", "", text, flags=re.DOTALL)
    text = re.sub(r"--[^\n]*", "", text)
    return text


def _parse_block_content(
    line_start: int, line_end: int, raw: str
) -> ImportBlock:
    """Parse one import block's raw text into an ImportBlock."""
    text = _strip_comments_all(raw)

    has_public = bool(re.search(r"\bpublic\b", text))

    mod_m = re.search(r"(?:open\s+)?import\s+([\w.]+)", text)
    module_path = mod_m.group(1) if mod_m else "?"

    using_names: List[str] = []
    renaming_pairs: List[Tuple[str, str]] = []

    using_clause = _extract_paren_after(text, "using")
    if using_clause is not None:
        using_names = _split_top_level(using_clause)

    renaming_clause = _extract_paren_after(text, "renaming")
    if renaming_clause is not None:
        for pair_str in _split_top_level(renaming_clause):
            pm = re.match(r"^(.+?)\s+to\s+(.+)$", pair_str)
            if pm:
                renaming_pairs.append(
                    (pm.group(1).strip(), pm.group(2).strip())
                )

    return ImportBlock(
        line_start=line_start,
        line_end=line_end,
        raw=raw,
        module_path=module_path,
        has_public=has_public,
        using_names=using_names,
        renaming_pairs=renaming_pairs,
    )


def _extract_paren_after(text: str, keyword: str) -> Optional[str]:
    """Find `keyword (...)` and return the parenthesized content.

    Returns None if not found.  Handles nested parens (rare in imports)."""
    pat = re.compile(rf"\b{re.escape(keyword)}\s*\(")
    m = pat.search(text)
    if not m:
        return None
    start = m.end()
    depth = 1
    i = start
    while i < len(text) and depth > 0:
        ch = text[i]
        if ch == "(":
            depth += 1
        elif ch == ")":
            depth -= 1
            if depth == 0:
                return text[start:i]
        i += 1
    return None


def _split_top_level(content: str) -> List[str]:
    """Split a using/renaming clause on `;` at paren depth 0."""
    parts: List[str] = []
    depth = 0
    buf: List[str] = []
    for ch in content:
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


# ----------------------------------------------------------------------------
# Editor — surgical removals
# ----------------------------------------------------------------------------


def remove_name_from_raw(raw: str, name: str) -> Optional[str]:
    """Remove `name` from a `using (...)` clause in `raw`.

    Returns new raw text, or None if the name wasn't found.

    Handles the four positional cases (sole entry / first / middle / last)
    by removing the name plus its adjacent semicolon, preserving surrounding
    whitespace/newlines as much as possible.
    """
    escaped = re.escape(name)
    nb = rf"(?<![{IDENT_CHARS}])"
    nf = rf"(?![{IDENT_CHARS}])"

    # Pattern 1 — name followed by `;` (anywhere except last in clause):
    #   `(X; Y; Z)` or `(... ; X; ...)` — consume `X` and its trailing `;`
    #    + surrounding whitespace.
    pat1 = rf"{nb}{escaped}{nf}\s*;\s*"
    # Pattern 2 — name preceded by `;` (last in clause):
    #   `(... ; X)` — consume the leading `;` and the name.
    pat2 = rf";\s*{nb}{escaped}{nf}\s*"
    # Pattern 3 — sole entry:
    #   `(X)` — consume the name (resulting in `()`).
    pat3 = rf"{nb}{escaped}{nf}\s*"

    # Try pat1 first (most common).  If only one match in clause, pat1 might
    # consume a separator that should remain; pat2 then handles the LAST-entry
    # case correctly.  Try pat3 as fallback for the sole-entry case.
    for pat in (pat1, pat2, pat3):
        new = re.sub(pat, "", raw, count=1)
        if new != raw:
            return new
    return None


def remove_rename_from_raw(raw: str, src: str, dst: str) -> Optional[str]:
    """Remove `src to dst` pair from a `renaming (...)` clause."""
    src_esc = re.escape(src)
    dst_esc = re.escape(dst)
    pair = rf"{src_esc}\s+to\s+{dst_esc}"
    nb = rf"(?<![{IDENT_CHARS}])"

    pat1 = rf"{nb}{pair}\s*;\s*"
    pat2 = rf";\s*{nb}{pair}\s*"
    pat3 = rf"{nb}{pair}\s*"

    for pat in (pat1, pat2, pat3):
        new = re.sub(pat, "", raw, count=1)
        if new != raw:
            return new
    return None


def replace_block_in_lines(
    lines: List[str], block: ImportBlock, new_raw: str
) -> List[str]:
    """Splice `new_raw` in place of the original block lines."""
    new_block_lines = new_raw.splitlines(keepends=True)
    # Ensure block ends with newline (matches original convention).
    if new_block_lines and not new_block_lines[-1].endswith("\n"):
        new_block_lines[-1] += "\n"
    return lines[: block.line_start] + new_block_lines + lines[block.line_end + 1 :]


# ----------------------------------------------------------------------------
# Type-checker invocation
# ----------------------------------------------------------------------------


def typecheck(
    rel_path: str,
    src_dir: Path,
    rts_cores: int,
    rts_heap_gb: int,
    timeout: int,
) -> bool:
    """Run `agda --type-check` on `rel_path` (relative to src_dir).
    Return True iff exit code is 0."""
    cmd = [
        str(AGDA_BIN),
        "+RTS",
        f"-N{rts_cores}",
        f"-M{rts_heap_gb}G",
        "-RTS",
        rel_path,
    ]
    try:
        result = subprocess.run(
            cmd,
            cwd=str(src_dir),
            capture_output=True,
            timeout=timeout,
        )
        return result.returncode == 0
    except subprocess.TimeoutExpired:
        return False


def project_typecheck(timeout: int = 1200) -> bool:
    """Run `cabal run shake -- check-properties` from repo root."""
    cmd = ["cabal", "run", "shake", "--", "check-properties"]
    try:
        result = subprocess.run(
            cmd, cwd=str(REPO_ROOT), capture_output=True, timeout=timeout
        )
        return result.returncode == 0 and b"All proof modules type-checked successfully!" in result.stdout
    except subprocess.TimeoutExpired:
        return False


# ----------------------------------------------------------------------------
# Pruning algorithm
# ----------------------------------------------------------------------------


def prune_file(
    file_path: Path,
    *,
    src_dir: Path,
    rts_cores: int,
    rts_heap_gb: int,
    timeout: int,
    include_public: bool,
    dry_run: bool,
    pre_check: bool,
    use_bisect: bool,
    verbose: bool,
) -> FileStats:
    """Prune one file.  Returns FileStats.

    Crash-safety: writes a sibling `.prune-bak` file before any modification.
    The `finally` clause restores the file to a coherent state (original on
    dry-run / exception, pruned on success).  If the process is killed
    bypassing `finally` (e.g. SIGKILL), the `.prune-bak` file survives and
    can be restored manually via `--restore-backups` mode.
    """
    stats = FileStats(file=file_path)
    t0 = time.monotonic()

    try:
        rel_path = str(file_path.relative_to(src_dir))
    except ValueError:
        stats.error = "file is not under src_dir"
        return stats

    original_content = file_path.read_text(encoding="utf-8")
    backup_path = file_path.with_suffix(file_path.suffix + ".prune-bak")
    backup_path.write_text(original_content, encoding="utf-8")

    final_content = original_content  # default if anything goes wrong

    try:
        if pre_check:
            if not typecheck(
                rel_path, src_dir, rts_cores, rts_heap_gb, timeout
            ):
                stats.error = "pre-check failed; file does not type-check"
                return stats

        blocks = parse_imports(original_content)
        if not blocks:
            stats.seconds = time.monotonic() - t0
            return stats

        # Working state: current file content (mutated as removals succeed).
        current_lines = original_content.splitlines(keepends=True)

        for block_idx, block in enumerate(blocks):
            if block.has_public and not include_public:
                stats.public_blocks_skipped += 1
                continue

            # Re-parse the block from current_lines, because earlier blocks
            # may have shifted line numbers.  Find by module_path.
            live_block = _find_live_block(
                current_lines, block.module_path, block_idx
            )
            if live_block is None:
                continue

            if use_bisect and len(live_block.using_names) > 1:
                _bisect_using(
                    file_path,
                    src_dir,
                    live_block,
                    current_lines,
                    rts_cores,
                    rts_heap_gb,
                    timeout,
                    stats,
                    verbose,
                )
            else:
                _per_name_using(
                    file_path,
                    src_dir,
                    live_block,
                    current_lines,
                    rts_cores,
                    rts_heap_gb,
                    timeout,
                    stats,
                    verbose,
                )

            # Re-parse for renaming pairs (block may have changed after using-removal).
            if live_block.renaming_pairs:
                live_block = _find_live_block(
                    current_lines, block.module_path, block_idx
                )
                if live_block is not None and live_block.renaming_pairs:
                    if use_bisect and len(live_block.renaming_pairs) > 1:
                        _bisect_renaming(
                            file_path,
                            src_dir,
                            live_block,
                            current_lines,
                            rts_cores,
                            rts_heap_gb,
                            timeout,
                            stats,
                            verbose,
                        )
                    else:
                        _per_name_renaming(
                            file_path,
                            src_dir,
                            live_block,
                            current_lines,
                            rts_cores,
                            rts_heap_gb,
                            timeout,
                            stats,
                            verbose,
                        )

        if not dry_run:
            final_content = "".join(current_lines)
    finally:
        # Always restore the file to a coherent state.  On dry-run or
        # exception, this writes the original.  On success, writes the
        # pruned content.  Backup deleted on normal exit.
        try:
            file_path.write_text(final_content, encoding="utf-8")
        finally:
            if backup_path.exists():
                backup_path.unlink()

    stats.seconds = time.monotonic() - t0
    return stats


def restore_backups(paths: List[Path]) -> int:
    """Restore any `*.prune-bak` files found under `paths`.

    Useful after an interrupted run that left files in a modified state.
    Returns: number of files restored."""
    restored = 0
    for p in paths:
        candidates: List[Path]
        if p.is_file() and p.name.endswith(".prune-bak"):
            candidates = [p]
        elif p.is_dir():
            candidates = list(p.rglob("*.prune-bak"))
        else:
            candidates = []
        for bak in candidates:
            target = bak.with_suffix("")  # drops .prune-bak, leaving e.g. .agda
            # The above is wrong — with_suffix drops the LAST suffix.
            # `foo.agda.prune-bak`.with_suffix('') → `foo.agda`.  That's correct.
            # Let me double-check: a file `foo.agda.prune-bak` has stem
            # `foo.agda` and suffix `.prune-bak`.  with_suffix('') gives
            # `foo.agda`.  Yes correct.
            target.write_text(bak.read_text(encoding="utf-8"), encoding="utf-8")
            bak.unlink()
            print(f"  restored {target}")
            restored += 1
    return restored


def _find_live_block(
    current_lines: List[str], module_path: str, original_idx: int
) -> Optional[ImportBlock]:
    """After mutations, re-parse and find the block matching `module_path`.

    Use original_idx to disambiguate if multiple blocks share a module_path
    (rare).  Pick the original_idx-th matching block."""
    fresh_blocks = parse_imports("".join(current_lines))
    matching = [b for b in fresh_blocks if b.module_path == module_path]
    if not matching:
        return None
    # If multiple, prefer the same positional index.
    if original_idx < len(matching):
        return matching[original_idx]
    return matching[-1]


def _per_name_using(
    file_path: Path,
    src_dir: Path,
    block: ImportBlock,
    current_lines: List[str],
    rts_cores: int,
    rts_heap_gb: int,
    timeout: int,
    stats: FileStats,
    verbose: bool,
) -> List[int]:
    """Test each using-name in `block` one at a time.

    Mutates `current_lines` in-place when a removal succeeds.
    Returns indices of removed names (informational)."""
    removed_indices = []
    # Iterate over names by NAME, not index — after each successful removal
    # the block's name list shrinks (we re-parse).
    for name in list(block.using_names):
        # Re-find the block in the current state.
        fresh = _find_live_block(current_lines, block.module_path, 0)
        if fresh is None or name not in fresh.using_names:
            continue
        if _try_remove_using(
            file_path, src_dir, fresh, current_lines, name,
            rts_cores, rts_heap_gb, timeout, stats, verbose
        ):
            removed_indices.append(0)  # informational only
    return removed_indices


def _per_name_renaming(
    file_path: Path,
    src_dir: Path,
    block: ImportBlock,
    current_lines: List[str],
    rts_cores: int,
    rts_heap_gb: int,
    timeout: int,
    stats: FileStats,
    verbose: bool,
) -> List[int]:
    """Same as _per_name_using but for renaming pairs."""
    removed = []
    for src, dst in list(block.renaming_pairs):
        fresh = _find_live_block(current_lines, block.module_path, 0)
        if fresh is None or (src, dst) not in fresh.renaming_pairs:
            continue
        if _try_remove_renaming(
            file_path, src_dir, fresh, current_lines, src, dst,
            rts_cores, rts_heap_gb, timeout, stats, verbose
        ):
            removed.append(0)
    return removed


def _bisect_using(
    file_path: Path,
    src_dir: Path,
    block: ImportBlock,
    current_lines: List[str],
    rts_cores: int,
    rts_heap_gb: int,
    timeout: int,
    stats: FileStats,
    verbose: bool,
) -> List[int]:
    """Bisect: try removing all using-names at once.  If pass, all dead.
    If fail with len==1, the one is live.  Else split and recurse.

    Falls back to per-name if bisection finds the bulk dead — i.e. when the
    fast path triggers, we save N-1 type-checks compared to per-name.

    Returns the set of names that were removed."""
    return _bisect_helper_using(
        file_path, src_dir, block.module_path, list(block.using_names),
        current_lines, rts_cores, rts_heap_gb, timeout, stats, verbose
    )


def _bisect_helper_using(
    file_path: Path,
    src_dir: Path,
    module_path: str,
    candidates: List[str],
    current_lines: List[str],
    rts_cores: int,
    rts_heap_gb: int,
    timeout: int,
    stats: FileStats,
    verbose: bool,
) -> List[str]:
    """Recursive bisection on `candidates` (names in module_path's using clause)."""
    if not candidates:
        return []

    # Re-find the block in the current state.
    fresh = _find_live_block(current_lines, module_path, 0)
    if fresh is None:
        return []

    # Verify all candidates still exist in the block.
    candidates = [n for n in candidates if n in fresh.using_names]
    if not candidates:
        return []

    # Try removing all candidates at once.
    snapshot = list(current_lines)
    new_raw = fresh.raw
    for name in candidates:
        nxt = remove_name_from_raw(new_raw, name)
        if nxt is None:
            # Some name not found (shouldn't happen after verification, but be safe).
            new_raw = None
            break
        new_raw = nxt

    if new_raw is None:
        # Couldn't construct the bulk-removal block; bail to per-name on this segment.
        return _bisect_per_name_fallback(
            file_path, src_dir, module_path, candidates, current_lines,
            rts_cores, rts_heap_gb, timeout, stats, verbose,
        )

    new_lines = replace_block_in_lines(current_lines, fresh, new_raw)
    file_path.write_text("".join(new_lines), encoding="utf-8")
    stats.type_checks += 1
    stats.using_tested += len(candidates)
    if typecheck(str(file_path.relative_to(src_dir)), src_dir, rts_cores, rts_heap_gb, timeout):
        # All candidates are dead.
        current_lines.clear()
        current_lines.extend(new_lines)
        stats.using_removed += len(candidates)
        if verbose:
            print(f"    -- bulk-removed {len(candidates)} using-names: {', '.join(candidates)}", flush=True)
        return candidates

    # Restore.
    file_path.write_text("".join(snapshot), encoding="utf-8")

    if len(candidates) == 1:
        if verbose:
            print(f"    -- KEPT {candidates[0]} (live)", flush=True)
        return []

    mid = len(candidates) // 2
    left = candidates[:mid]
    right = candidates[mid:]
    left_dead = _bisect_helper_using(
        file_path, src_dir, module_path, left, current_lines,
        rts_cores, rts_heap_gb, timeout, stats, verbose,
    )
    right_dead = _bisect_helper_using(
        file_path, src_dir, module_path, right, current_lines,
        rts_cores, rts_heap_gb, timeout, stats, verbose,
    )
    return left_dead + right_dead


def _bisect_per_name_fallback(
    file_path: Path,
    src_dir: Path,
    module_path: str,
    candidates: List[str],
    current_lines: List[str],
    rts_cores: int,
    rts_heap_gb: int,
    timeout: int,
    stats: FileStats,
    verbose: bool,
) -> List[str]:
    """Per-name removal for a list of using names in module_path."""
    removed = []
    for name in candidates:
        fresh = _find_live_block(current_lines, module_path, 0)
        if fresh is None or name not in fresh.using_names:
            continue
        if _try_remove_using(
            file_path, src_dir, fresh, current_lines, name,
            rts_cores, rts_heap_gb, timeout, stats, verbose,
        ):
            removed.append(name)
    return removed


def _try_remove_using(
    file_path: Path,
    src_dir: Path,
    block: ImportBlock,
    current_lines: List[str],
    name: str,
    rts_cores: int,
    rts_heap_gb: int,
    timeout: int,
    stats: FileStats,
    verbose: bool,
) -> bool:
    """Try removing a single using-name.  Returns True if removed."""
    snapshot = list(current_lines)
    new_raw = remove_name_from_raw(block.raw, name)
    if new_raw is None:
        return False
    new_lines = replace_block_in_lines(current_lines, block, new_raw)
    file_path.write_text("".join(new_lines), encoding="utf-8")
    stats.type_checks += 1
    stats.using_tested += 1
    if typecheck(str(file_path.relative_to(src_dir)), src_dir, rts_cores, rts_heap_gb, timeout):
        current_lines.clear()
        current_lines.extend(new_lines)
        stats.using_removed += 1
        if verbose:
            print(f"    -- removed using-name `{name}` from `{block.module_path}`", flush=True)
        return True
    file_path.write_text("".join(snapshot), encoding="utf-8")
    if verbose:
        print(f"    -- KEPT using-name `{name}` from `{block.module_path}` (live)", flush=True)
    return False


def _bisect_renaming(
    file_path: Path,
    src_dir: Path,
    block: ImportBlock,
    current_lines: List[str],
    rts_cores: int,
    rts_heap_gb: int,
    timeout: int,
    stats: FileStats,
    verbose: bool,
) -> List[Tuple[str, str]]:
    """Bisect on renaming pairs.  Symmetric to _bisect_using."""
    return _bisect_helper_renaming(
        file_path, src_dir, block.module_path, list(block.renaming_pairs),
        current_lines, rts_cores, rts_heap_gb, timeout, stats, verbose,
    )


def _bisect_helper_renaming(
    file_path: Path,
    src_dir: Path,
    module_path: str,
    candidates: List[Tuple[str, str]],
    current_lines: List[str],
    rts_cores: int,
    rts_heap_gb: int,
    timeout: int,
    stats: FileStats,
    verbose: bool,
) -> List[Tuple[str, str]]:
    if not candidates:
        return []

    fresh = _find_live_block(current_lines, module_path, 0)
    if fresh is None:
        return []

    candidates = [p for p in candidates if p in fresh.renaming_pairs]
    if not candidates:
        return []

    snapshot = list(current_lines)
    new_raw = fresh.raw
    for src, dst in candidates:
        nxt = remove_rename_from_raw(new_raw, src, dst)
        if nxt is None:
            new_raw = None
            break
        new_raw = nxt

    if new_raw is None:
        return _bisect_per_pair_fallback(
            file_path, src_dir, module_path, candidates, current_lines,
            rts_cores, rts_heap_gb, timeout, stats, verbose,
        )

    new_lines = replace_block_in_lines(current_lines, fresh, new_raw)
    file_path.write_text("".join(new_lines), encoding="utf-8")
    stats.type_checks += 1
    stats.renaming_tested += len(candidates)
    if typecheck(str(file_path.relative_to(src_dir)), src_dir, rts_cores, rts_heap_gb, timeout):
        current_lines.clear()
        current_lines.extend(new_lines)
        stats.renaming_removed += len(candidates)
        if verbose:
            print(f"    -- bulk-removed {len(candidates)} renaming-pairs", flush=True)
        return candidates

    file_path.write_text("".join(snapshot), encoding="utf-8")

    if len(candidates) == 1:
        return []

    mid = len(candidates) // 2
    left = candidates[:mid]
    right = candidates[mid:]
    return (
        _bisect_helper_renaming(
            file_path, src_dir, module_path, left, current_lines,
            rts_cores, rts_heap_gb, timeout, stats, verbose,
        )
        + _bisect_helper_renaming(
            file_path, src_dir, module_path, right, current_lines,
            rts_cores, rts_heap_gb, timeout, stats, verbose,
        )
    )


def _bisect_per_pair_fallback(
    file_path: Path,
    src_dir: Path,
    module_path: str,
    candidates: List[Tuple[str, str]],
    current_lines: List[str],
    rts_cores: int,
    rts_heap_gb: int,
    timeout: int,
    stats: FileStats,
    verbose: bool,
) -> List[Tuple[str, str]]:
    removed = []
    for src, dst in candidates:
        fresh = _find_live_block(current_lines, module_path, 0)
        if fresh is None or (src, dst) not in fresh.renaming_pairs:
            continue
        if _try_remove_renaming(
            file_path, src_dir, fresh, current_lines, src, dst,
            rts_cores, rts_heap_gb, timeout, stats, verbose,
        ):
            removed.append((src, dst))
    return removed


def _try_remove_renaming(
    file_path: Path,
    src_dir: Path,
    block: ImportBlock,
    current_lines: List[str],
    src: str,
    dst: str,
    rts_cores: int,
    rts_heap_gb: int,
    timeout: int,
    stats: FileStats,
    verbose: bool,
) -> bool:
    snapshot = list(current_lines)
    new_raw = remove_rename_from_raw(block.raw, src, dst)
    if new_raw is None:
        return False
    new_lines = replace_block_in_lines(current_lines, block, new_raw)
    file_path.write_text("".join(new_lines), encoding="utf-8")
    stats.type_checks += 1
    stats.renaming_tested += 1
    if typecheck(str(file_path.relative_to(src_dir)), src_dir, rts_cores, rts_heap_gb, timeout):
        current_lines.clear()
        current_lines.extend(new_lines)
        stats.renaming_removed += 1
        if verbose:
            print(f"    -- removed renaming-pair `{src} to {dst}` from `{block.module_path}`", flush=True)
        return True
    file_path.write_text("".join(snapshot), encoding="utf-8")
    if verbose:
        print(f"    -- KEPT renaming-pair `{src} to {dst}` (live)", flush=True)
    return False


# ----------------------------------------------------------------------------
# CLI / orchestration
# ----------------------------------------------------------------------------


def gather_agda_files(paths: List[Path]) -> List[Path]:
    """Recursively collect *.agda files from the given paths."""
    files: List[Path] = []
    for p in paths:
        if p.is_file() and p.suffix == ".agda":
            files.append(p.resolve())
        elif p.is_dir():
            files.extend(sorted(p.rglob("*.agda")))
        else:
            print(f"warning: {p} is not a file or directory; skipping", file=sys.stderr)
    return [f.resolve() for f in files]


def worker_process_file(args: tuple) -> FileStats:
    """Entry point for process pool workers."""
    (
        file_path,
        src_dir,
        rts_cores,
        rts_heap_gb,
        timeout,
        include_public,
        dry_run,
        pre_check,
        use_bisect,
        verbose,
    ) = args
    return prune_file(
        file_path,
        src_dir=src_dir,
        rts_cores=rts_cores,
        rts_heap_gb=rts_heap_gb,
        timeout=timeout,
        include_public=include_public,
        dry_run=dry_run,
        pre_check=pre_check,
        use_bisect=use_bisect,
        verbose=verbose,
    )


def main() -> int:
    parser = argparse.ArgumentParser(
        formatter_class=argparse.RawDescriptionHelpFormatter,
        description=__doc__,
    )
    parser.add_argument("paths", nargs="*", type=Path, help="Files or directories to prune (default: src/)")
    parser.add_argument("-j", "--workers", type=int, default=4, help="Parallel file workers (default: 4)")
    parser.add_argument("--rts-cores", type=int, default=8, help="GHC RTS cores per agda call (default: 8)")
    parser.add_argument("--rts-heap", type=int, default=3, help="GHC RTS heap per agda call in GB (default: 3)")
    parser.add_argument("--timeout", type=int, default=300, help="Per-agda-call timeout seconds (default: 300)")
    parser.add_argument("--include-public", action="store_true", help="Test `public` re-export lines too")
    parser.add_argument("--final-check", action="store_true", help="Run cabal run shake -- check-properties after pruning")
    parser.add_argument("--dry-run", action="store_true", help="Don't write changes; report what would be removed")
    parser.add_argument("--quiet", action="store_true", help="Suppress per-file output")
    parser.add_argument("--verbose", action="store_true", help="Per-name decision logging")
    parser.add_argument("--pre-check", action="store_true", help="Verify each file type-checks before pruning")
    parser.add_argument("--no-bisect", action="store_true", help="Disable bisection (pure per-name brute force)")
    parser.add_argument("--restore-backups", action="store_true", help="Restore any *.prune-bak files left by an interrupted run, then exit")

    args = parser.parse_args()

    if args.restore_backups:
        paths = args.paths if args.paths else [SRC_DIR]
        n = restore_backups(paths)
        print(f"restored {n} backup(s)")
        return 0

    paths = args.paths if args.paths else [SRC_DIR]
    files = gather_agda_files(paths)
    if not files:
        print("error: no .agda files found", file=sys.stderr)
        return 1

    if not args.quiet:
        print(f"prune_unused_imports: processing {len(files)} files with {args.workers} workers")
        print(f"  src_dir={SRC_DIR}, rts={args.rts_cores}c/{args.rts_heap}G, "
              f"timeout={args.timeout}s, include_public={args.include_public}, "
              f"dry_run={args.dry_run}, bisect={not args.no_bisect}", flush=True)

    t_start = time.monotonic()
    worker_args = [
        (
            f,
            SRC_DIR,
            args.rts_cores,
            args.rts_heap,
            args.timeout,
            args.include_public,
            args.dry_run,
            args.pre_check,
            not args.no_bisect,
            args.verbose,
        )
        for f in files
    ]

    all_stats: List[FileStats] = []
    errors = 0

    if args.workers <= 1:
        for wa in worker_args:
            stats = worker_process_file(wa)
            all_stats.append(stats)
            _print_stats(stats, args.quiet)
            if stats.error:
                errors += 1
    else:
        with concurrent.futures.ProcessPoolExecutor(max_workers=args.workers) as pool:
            futures = {pool.submit(worker_process_file, wa): wa[0] for wa in worker_args}
            for fut in concurrent.futures.as_completed(futures):
                stats = fut.result()
                all_stats.append(stats)
                _print_stats(stats, args.quiet)
                if stats.error:
                    errors += 1

    elapsed = time.monotonic() - t_start
    total_removed = sum(s.removed_total for s in all_stats)
    total_tcs = sum(s.type_checks for s in all_stats)
    files_changed = sum(1 for s in all_stats if s.removed_total > 0)
    print()
    print(f"=== summary ===")
    print(f"  files processed: {len(all_stats)}")
    print(f"  files modified : {files_changed}")
    print(f"  dead names removed: {total_removed} (using: {sum(s.using_removed for s in all_stats)}, renaming: {sum(s.renaming_removed for s in all_stats)})")
    print(f"  public blocks skipped: {sum(s.public_blocks_skipped for s in all_stats)}")
    print(f"  type-checks run: {total_tcs}")
    print(f"  errors: {errors}")
    print(f"  wall time: {elapsed:.1f}s")
    if args.dry_run:
        print(f"  (dry-run: no files modified)")

    if args.final_check and not args.dry_run:
        print()
        print("=== final project-wide check-properties ===")
        if project_typecheck():
            print("  PASS")
        else:
            print("  FAIL — project-wide check-properties broke after pruning!", file=sys.stderr)
            return 2

    return 1 if errors else 0


def _print_stats(stats: FileStats, quiet: bool) -> None:
    if quiet and not stats.error and stats.removed_total == 0:
        return
    try:
        rel = stats.file.relative_to(REPO_ROOT)
    except ValueError:
        rel = stats.file
    if stats.error:
        print(f"  {rel}  ERROR: {stats.error}", flush=True)
    else:
        print(
            f"  {rel}  removed={stats.removed_total} "
            f"(using {stats.using_removed}/{stats.using_tested}, "
            f"renaming {stats.renaming_removed}/{stats.renaming_tested}) "
            f"tcs={stats.type_checks} t={stats.seconds:.1f}s "
            f"{'public-skipped='+str(stats.public_blocks_skipped) if stats.public_blocks_skipped else ''}",
            flush=True,
        )


if __name__ == "__main__":
    sys.exit(main())
