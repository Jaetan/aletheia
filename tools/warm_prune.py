"""Warm-engine flat dead-import prune (ci-speed branch).

Tests each imported name INDEPENDENTLY against the pristine file: remove the
name, reload in one persistent warm agda process, accept it as dead iff the file
re-checks with no new semantic-change warnings, then RESTORE the file.  A name
is dead iff removing it *alone* still type-checks; independently-dead names are
jointly removable (you cannot un-use code by deleting an unused import), so no
cumulative mutation is needed.

This is the exact, unwrapped spec -- "dead iff agda still type-checks without
it" -- with nothing to get wrong.  It replaces the previous bisection driver,
whose cumulative mutation + always-`find_live_block(..., 0)` block re-find
silently dropped candidates in files with two same-module imports or with a
multi-line block (a `using` clause continued by a `renaming` clause on the next
line) -- a coverage false-negative: it missed real dead imports.  Here each
block is addressed by its own parse_imports line range, so those cases are
handled correctly.

`open import M ... public` lines are skipped unless --include-public (removing a
re-exported name changes the file's exported surface, which needs downstream
consumer checks not performed here).  One serial warm process; holds the
repo-wide single-Agda lock so no concurrent Agda op can observe a file
mid-rewrite.  Invoke: `python -m tools.warm_prune [--apply] [--include-public]
[--verbose] <relpath.agda | dir> [...]`.  Check-only (the default) exits nonzero
when any dead import is found.
"""

from __future__ import annotations

import sys
import time
from pathlib import Path
from typing import TYPE_CHECKING, NamedTuple

from tools._agda_imports import (
    gather_agda_files,
    parse_imports,
    remove_name_from_raw,
    remove_rename_from_raw,
    replace_block_in_lines,
)
from tools._common import (
    agda_tree_lock,
    emit,
    install_restore_handlers,
    track_inflight,
    untrack_inflight,
)
from tools.warm_dead_imports import SRC, WarmAgda, count_semantic_warnings

if TYPE_CHECKING:
    from tools._agda_imports import ImportBlock


class Candidate(NamedTuple):
    """One removable name: a using-name, or a renaming pair, within `block`."""

    block: ImportBlock
    kind: str  # "using" | "renaming"
    name: str  # using-name; for renaming the bare destination (in-scope) name
    new_raw: str  # the block's raw with exactly this candidate removed


class FileCtx(NamedTuple):
    """The per-file invariants threaded through the audit of one file."""

    agda: WarmAgda
    file_path: Path
    original_lines: list[str]
    baseline_warnings: int


class Scan(NamedTuple):
    """Result of scanning one file's import blocks for dead names."""

    dead: list[Candidate]
    public_skipped: int


class FileResult(NamedTuple):
    """Outcome of auditing one file."""

    rel_path: str
    dead: list[Candidate]
    public_skipped: int
    error: str | None
    seconds: float


def _candidates(block: ImportBlock) -> list[Candidate]:
    """Every removable candidate in `block`, each carrying its block-removed raw."""
    out: list[Candidate] = []
    for name in block.using_names:
        new_raw = remove_name_from_raw(block.raw, name)
        if new_raw is not None:
            out.append(Candidate(block, "using", name, new_raw))
    for src, dst in block.renaming_pairs:
        new_raw = remove_rename_from_raw(block.raw, src, dst)
        if new_raw is not None:
            out.append(Candidate(block, "renaming", dst, new_raw))
    return out


def _is_dead(ctx: FileCtx, cand: Candidate) -> bool:
    """Remove `cand` from the pristine file, warm-reload, restore; dead iff clean.

    Writes the file with the candidate's block replaced by its removed raw, loads
    it in the warm process, then ALWAYS restores the original.  The candidate is
    dead iff the file still type-checks with no new semantic-change warnings.
    """
    original = "".join(ctx.original_lines)
    new_lines = replace_block_in_lines(ctx.original_lines, cand.block, cand.new_raw)
    track_inflight(str(ctx.file_path), original)
    try:
        _ = ctx.file_path.write_text("".join(new_lines), encoding="utf-8")
        result = ctx.agda.load(str(ctx.file_path))
    finally:
        _ = ctx.file_path.write_text(original, encoding="utf-8")
        untrack_inflight(str(ctx.file_path))
    return result.ok and count_semantic_warnings(result.warnings) <= ctx.baseline_warnings


def _collect_dead(ctx: FileCtx, *, include_public: bool, verbose: bool) -> Scan:
    """Scan every import block; return the independently-dead candidates."""
    dead: list[Candidate] = []
    public_skipped = 0
    for block in parse_imports("".join(ctx.original_lines)):
        if block.has_public and not include_public:
            public_skipped += 1
            continue
        for cand in _candidates(block):
            if _is_dead(ctx, cand):
                dead.append(cand)
                emit(f"    -- DEAD {cand.kind} `{cand.name}` from `{cand.block.module_path}`")
            elif verbose:
                emit(f"    -- live {cand.kind} `{cand.name}` from `{cand.block.module_path}`")
    return Scan(dead, public_skipped)


def _apply_removals(original_lines: list[str], dead: list[Candidate]) -> str:
    """Return `original_lines` with every dead candidate removed from its block.

    Groups dead names by block and rewrites each block's raw once, then splices
    blocks back in DESCENDING line order so earlier blocks' line offsets stay
    valid as later ones are replaced.
    """
    by_block: dict[int, list[Candidate]] = {}
    for cand in dead:
        by_block.setdefault(cand.block.line_start, []).append(cand)
    lines = list(original_lines)
    for line_start in sorted(by_block, reverse=True):
        cands = by_block[line_start]
        block = cands[0].block
        raw: str | None = block.raw
        for cand in cands:
            if raw is None:
                break
            if cand.kind == "using":
                raw = remove_name_from_raw(raw, cand.name)
            else:
                src = next(s for s, d in block.renaming_pairs if d == cand.name)
                raw = remove_rename_from_raw(raw, src, cand.name)
        if raw is not None:
            lines = replace_block_in_lines(lines, block, raw)
    return "".join(lines)


def _apply_and_confirm(ctx: FileCtx, dead: list[Candidate]) -> str | None:
    """Write the file with all `dead` names removed; confirm it still checks.

    Returns None on success, or an error string (after reverting) if the joint
    removal does not type-check.
    """
    original = "".join(ctx.original_lines)
    _ = ctx.file_path.write_text(_apply_removals(ctx.original_lines, dead), encoding="utf-8")
    confirm = ctx.agda.load(str(ctx.file_path))
    if confirm.ok and count_semantic_warnings(confirm.warnings) <= ctx.baseline_warnings:
        return None
    _ = ctx.file_path.write_text(original, encoding="utf-8")
    return "joint removal failed; reverted"


def audit_file(
    agda: WarmAgda,
    file_path: Path,
    *,
    include_public: bool,
    apply: bool,
    verbose: bool,
) -> FileResult:
    """Flat-independent dead-import audit of one file via the warm process."""
    t0 = time.monotonic()
    rel_path = str(file_path.relative_to(SRC))
    original_lines = file_path.read_text(encoding="utf-8").splitlines(keepends=True)
    baseline = agda.load(str(file_path))
    if not baseline.ok:
        return FileResult(rel_path, [], 0, "baseline type-check failed", time.monotonic() - t0)
    ctx = FileCtx(agda, file_path, original_lines, count_semantic_warnings(baseline.warnings))
    scan = _collect_dead(ctx, include_public=include_public, verbose=verbose)
    error = _apply_and_confirm(ctx, scan.dead) if apply and scan.dead else None
    return FileResult(rel_path, scan.dead, scan.public_skipped, error, time.monotonic() - t0)


def _resolve_files(args: list[str]) -> list[Path]:
    """Resolve CLI path args (src-relative or absolute) to a sorted .agda file list."""
    roots = [Path(a) if Path(a).is_absolute() else SRC / a for a in args]
    return gather_agda_files(roots)


_USAGE = (
    "usage: python -m tools.warm_prune [--apply] [--include-public] [--verbose] "
    "<relpath.agda | dir> [...]"
)


def main() -> int:
    """Warm flat-prune the given files/dirs; --apply writes, else check-only."""
    args = sys.argv[1:]
    apply = "--apply" in args
    include_public = "--include-public" in args
    verbose = "--verbose" in args
    rels = [a for a in args if not a.startswith("--")]
    files = _resolve_files(rels)
    if not files:
        emit(_USAGE)
        return 2

    install_restore_handlers()
    start = time.monotonic()
    n_dead = 0
    with agda_tree_lock(), WarmAgda() as agda:
        for file_path in files:
            result = audit_file(
                agda, file_path, include_public=include_public, apply=apply, verbose=verbose
            )
            n_dead += len(result.dead)
            tag = " APPLIED" if apply and result.dead else ""
            err = f"  ERROR={result.error}" if result.error else ""
            pub = f"  public-skipped={result.public_skipped}" if result.public_skipped else ""
            emit(
                f"{result.rel_path}: dead={len(result.dead)}{tag}{err}{pub}  "
                + f"({result.seconds:.1f}s)"
            )
    emit(
        f"=== warm-prune: {n_dead} dead import(s) across {len(files)} file(s) "
        + f"in {time.monotonic() - start:.1f}s ==="
    )
    return 1 if n_dead and not apply else 0


if __name__ == "__main__":
    sys.exit(main())
