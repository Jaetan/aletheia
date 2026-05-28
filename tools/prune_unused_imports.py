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

Run `tools/prune_unused_imports.py --help` for the full option list (the
argparse definition in `main` is the single source of truth).

The default mode tries removing ALL names in an import block at once
(bisection optimization).  If that fails, it falls back to per-name
testing for that block.  Best case: 1 type-check per all-dead block.
Worst case: 1 + N type-checks per block where N is the block's name count.

Output: per-file summary line + aggregate stats.  Exit 0 if all files
processed successfully; 1 if any failures.
"""

from __future__ import annotations

import argparse
import atexit
import concurrent.futures
import signal
import subprocess
import sys
import time
from dataclasses import dataclass, field
from pathlib import Path

from tools._agda_imports import (
    AGDA_BIN,
    REPO_ROOT,
    SRC_DIR,
    ImportBlock,
    TypecheckCtx,
    build_reverse_dep_graph,
    check_modified,
    find_live_block,
    gather_agda_files,
    parse_imports,
    path_to_module,
    prefill_consumer_baselines,
    remove_name_from_raw,
    remove_rename_from_raw,
    replace_block_in_lines,
    set_block_check_context,
    topological_levels,
    typecheck,
    warning_count_for,
)
from tools._common import emit, find_executable

# Names imported above and re-exported here because ``tools.warm_dead_imports``
# imports them from this module; ``__all__`` marks them as intentional exports.
__all__ = [
    "AGDA_BIN",
    "SRC_DIR",
    "ImportBlock",
    "TypecheckCtx",
    "parse_imports",
    "prune_file",
    "remove_name_from_raw",
    "remove_rename_from_raw",
    "replace_block_in_lines",
    "typecheck",
    "warning_count_for",
]

# ----------------------------------------------------------------------------
# Constants and data model
# ----------------------------------------------------------------------------

# How many topo-level batch sizes to show in the batching summary before
# eliding the rest with an ellipsis.
_BATCH_PREVIEW_LIMIT = 10


@dataclass
class ImportCounts:
    """How many names in one clause kind were tested for removal, and removed."""

    tested: int = 0
    removed: int = 0


@dataclass
class Tally:
    """The activity counters for one file's audit (names + agda invocations)."""

    using: ImportCounts = field(default_factory=ImportCounts)
    renaming: ImportCounts = field(default_factory=ImportCounts)
    public_blocks_skipped: int = 0
    type_checks: int = 0


@dataclass
class FileStats:
    """Per-file pruning result: activity tally plus timing and error state."""

    file: Path
    tally: Tally = field(default_factory=Tally)
    seconds: float = 0.0
    baseline_warnings: int = 0
    error: str | None = None

    @property
    def removed_total(self) -> int:
        """Total names removed across both using and renaming clauses."""
        return self.tally.using.removed + self.tally.renaming.removed


@dataclass(frozen=True)
class PruneConfig:
    """The per-run pruning configuration shared by every file worker.

    Bundles the agda invocation context (``ctx``) with the run-wide flags so a
    single value threads through ``worker_process_file`` -> ``prune_file``
    instead of a dozen positional arguments.  ``consumers_map`` is the
    module-name -> importers graph used only when ``include_public`` is set (it
    is ``None`` otherwise); the other flags mirror the CLI switches.
    """

    ctx: TypecheckCtx
    include_public: bool
    dry_run: bool
    use_bisect: bool
    verbose: bool
    consumers_map: dict[str, list[Path]] | None = None


@dataclass
class BisectState:
    """The per-file mutable working state threaded through the bisect helpers.

    ``current_lines`` is the file's content as a line list, mutated in place as
    removals are accepted; ``stats`` accumulates the per-file counters; ``verbose``
    toggles per-name decision logging.  Bundling them keeps each recursive bisect
    helper's signature small (the alternative is threading four positional
    arguments through a dozen mutually-recursive functions).
    """

    file_path: Path
    current_lines: list[str]
    stats: FileStats
    verbose: bool


def project_typecheck(timeout: int = 1200) -> bool:
    """Run ``cabal run shake -- check-properties`` from repo root."""
    cmd = [find_executable("cabal"), "run", "shake", "--", "check-properties"]
    try:
        result = subprocess.run(
            cmd, check=False, cwd=str(REPO_ROOT), capture_output=True, timeout=timeout
        )
    except subprocess.TimeoutExpired:
        return False
    return (
        result.returncode == 0 and b"All proof modules type-checked successfully!" in result.stdout
    )


# ----------------------------------------------------------------------------
# Pruning algorithm
# ----------------------------------------------------------------------------


def _block_consumers_for(
    block: ImportBlock,
    file_consumers: list[Path],
    consumer_baselines: dict[Path, int],
    config: PruneConfig,
) -> None:
    """Arm the process-local consumer-check context for one block.

    When ``block`` has ``public`` AND ``--include-public`` is on, every
    removal-attempt also re-checks this file's direct consumers (removing a
    name from a public block changes the file's exported surface), so their
    pre-modification baselines are prefilled once.  Otherwise the consumer
    list is emptied (no extra work).
    """
    if block.has_public and config.include_public and file_consumers:
        prefill_consumer_baselines(file_consumers, consumer_baselines, config.ctx)
        set_block_check_context(file_consumers, consumer_baselines)
    else:
        set_block_check_context([], consumer_baselines)


def _prune_one_block(
    state: BisectState,
    config: PruneConfig,
    block: ImportBlock,
    block_idx: int,
) -> None:
    """Audit a single import block: using-names then renaming pairs.

    ``block`` is the snapshot parsed from the original content; it is re-found
    in the live line list (earlier blocks may have shifted line numbers) before
    each phase.  Mutates ``state.current_lines`` in place as removals succeed.
    """
    live_block = find_live_block(state.current_lines, block.module_path, block_idx)
    if live_block is None:
        return

    if config.use_bisect and len(live_block.using_names) > 1:
        _ = _bisect_using(state, config.ctx, live_block)
    else:
        _per_name_using(state, config.ctx, live_block)

    # Re-parse for renaming pairs (block may have changed after using-removal).
    if not live_block.renaming_pairs:
        return
    live_block = find_live_block(state.current_lines, block.module_path, block_idx)
    if live_block is None or not live_block.renaming_pairs:
        return
    if config.use_bisect and len(live_block.renaming_pairs) > 1:
        _ = _bisect_renaming(state, config.ctx, live_block)
    else:
        _per_name_renaming(state, config.ctx, live_block)


def _file_consumers_for(file_path: Path, config: PruneConfig) -> list[Path]:
    """List the direct consumers of ``file_path`` from the reverse-dep graph.

    Empty unless ``--include-public`` is on with a graph; uses the file's own
    module path and excludes the file itself.
    """
    if not (config.include_public and config.consumers_map is not None):
        return []
    file_module = path_to_module(file_path, config.ctx.src_dir)
    return [c for c in config.consumers_map.get(file_module, []) if c != file_path]


def _audit_file(rel_path: str, original_content: str, config: PruneConfig, stats: FileStats) -> str:
    """Audit one file's import blocks, returning the resulting file content.

    Computes the warning baseline (always — to detect silent pattern-shadowing),
    then walks each block dropping dead names.  On a baseline failure sets
    ``stats.error`` and returns ``original_content`` unchanged; otherwise returns
    the pruned content (or the original under ``--dry-run``).
    """
    baseline_warnings = warning_count_for(rel_path, config.ctx)
    if baseline_warnings < 0:
        stats.error = "baseline type-check failed; file does not type-check"
        return original_content
    stats.baseline_warnings = baseline_warnings

    blocks = parse_imports(original_content)
    if not blocks:
        return original_content

    file_consumers = _file_consumers_for(stats.file, config)
    consumer_baselines: dict[Path, int] = {}
    state = BisectState(
        file_path=stats.file,
        current_lines=original_content.splitlines(keepends=True),
        stats=stats,
        verbose=config.verbose,
    )

    for block_idx, block in enumerate(blocks):
        if block.has_public and not config.include_public:
            stats.tally.public_blocks_skipped += 1
            continue
        _block_consumers_for(block, file_consumers, consumer_baselines, config)
        _prune_one_block(state, config, block, block_idx)

    return original_content if config.dry_run else "".join(state.current_lines)


def prune_file(file_path: Path, config: PruneConfig) -> FileStats:
    """Prune one file.  Returns FileStats.

    Crash-safety: writes a sibling ``.prune-bak`` file before any modification.
    The ``finally`` clause restores the file to a coherent state (original on
    dry-run / exception, pruned on success).  If the process is killed
    bypassing ``finally`` (e.g. SIGKILL), the ``.prune-bak`` file survives and
    can be restored manually via ``--restore-backups`` mode.
    """
    stats = FileStats(file=file_path)
    t0 = time.monotonic()

    try:
        rel_path = str(file_path.relative_to(config.ctx.src_dir))
    except ValueError:
        stats.error = "file is not under src_dir"
        return stats

    original_content = file_path.read_text(encoding="utf-8")
    backup_path = file_path.with_suffix(file_path.suffix + ".prune-bak")
    _ = backup_path.write_text(original_content, encoding="utf-8")

    final_content = original_content  # default if anything goes wrong
    try:
        final_content = _audit_file(rel_path, original_content, config, stats)
    finally:
        # Always restore the file to a coherent state.  On dry-run or
        # exception, this writes the original.  On success, writes the
        # pruned content.  Backup deleted on normal exit.
        try:
            _ = file_path.write_text(final_content, encoding="utf-8")
        finally:
            if backup_path.exists():
                backup_path.unlink()

    stats.seconds = time.monotonic() - t0
    return stats


def restore_backups(paths: list[Path]) -> int:
    """Restore any `*.prune-bak` files found under `paths`.

    Useful after an interrupted run that left files in a modified state.
    Returns: number of files restored.
    """
    restored = 0
    for p in paths:
        candidates: list[Path]
        if p.is_file() and p.name.endswith(".prune-bak"):
            candidates = [p]
        elif p.is_dir():
            candidates = list(p.rglob("*.prune-bak"))
        else:
            candidates = []
        for bak in candidates:
            # `foo.agda.prune-bak`.with_suffix("") drops only the LAST suffix,
            # restoring the original `foo.agda` path.
            target = bak.with_suffix("")
            _ = target.write_text(bak.read_text(encoding="utf-8"), encoding="utf-8")
            bak.unlink()
            emit(f"  restored {target}")
            restored += 1
    return restored


# --- Crash-safe cleanup (user request 2026-05-26) ---------------------------
# The per-file `finally` restores on normal completion/exception, but a
# SIGTERM/SIGINT (e.g. `timeout`, Ctrl-C) bypasses it, leaving the source
# modified + a stray `.prune-bak` (this corrupted a working tree once).  These
# handlers restore any stray backup under SRC_DIR on exit/signal;
# restore_backups() scans the filesystem, so a single main-process handler also
# recovers backups left by ProcessPool workers.  SIGKILL can't be caught — the
# start-of-run sweep (in main) catches its leftovers on the next invocation.
def _cleanup_stray_backups() -> int:
    return restore_backups([SRC_DIR])


def _signal_cleanup(signum: int, _frame: object) -> None:
    _cleanup_stray_backups()
    sys.exit(128 + signum)


def _install_cleanup_handlers() -> None:
    atexit.register(_cleanup_stray_backups)
    for _sig in (signal.SIGINT, signal.SIGTERM):
        signal.signal(_sig, _signal_cleanup)


def _per_name_using(state: BisectState, ctx: TypecheckCtx, block: ImportBlock) -> None:
    """Test each using-name in ``block`` one at a time.

    Mutates ``state.current_lines`` in place when a removal succeeds.
    """
    # Iterate over names by NAME, not index — after each successful removal
    # the block's name list shrinks (we re-parse).
    for name in list(block.using_names):
        # Re-find the block in the current state.
        fresh = find_live_block(state.current_lines, block.module_path, 0)
        if fresh is None or name not in fresh.using_names:
            continue
        _ = _try_remove_using(state, ctx, fresh, name)


def _per_name_renaming(state: BisectState, ctx: TypecheckCtx, block: ImportBlock) -> None:
    """Test each renaming pair in ``block`` one at a time (mirror of using)."""
    for src, dst in list(block.renaming_pairs):
        fresh = find_live_block(state.current_lines, block.module_path, 0)
        if fresh is None or (src, dst) not in fresh.renaming_pairs:
            continue
        _ = _try_remove_renaming(state, ctx, fresh, src, dst)


def _bisect_using(state: BisectState, ctx: TypecheckCtx, block: ImportBlock) -> list[str]:
    """Bisect: try removing all using-names at once.

    If the bulk removal passes, all are dead.  If it fails with len==1, that
    one is live.  Otherwise split and recurse.  When the fast path triggers we
    save N-1 type-checks compared to per-name.  Returns the names removed.
    """
    return _bisect_helper_using(state, ctx, block.module_path, list(block.using_names))


def _try_bulk_remove_using(
    state: BisectState,
    ctx: TypecheckCtx,
    fresh: ImportBlock,
    candidates: list[str],
) -> bool | None:
    """Attempt to drop ALL ``candidates`` from ``fresh`` in one type-check.

    Returns True if every candidate is dead (changes accepted), False if the
    bulk removal does not type-check (file restored), or None if the bulk-removed
    block text could not even be constructed (caller falls back to per-name).
    """
    new_raw: str | None = fresh.raw
    for name in candidates:
        nxt = remove_name_from_raw(new_raw, name)
        if nxt is None:
            return None
        new_raw = nxt

    snapshot = list(state.current_lines)
    new_lines = replace_block_in_lines(state.current_lines, fresh, new_raw)
    _ = state.file_path.write_text("".join(new_lines), encoding="utf-8")
    state.stats.tally.type_checks += 1
    state.stats.tally.using.tested += len(candidates)
    if check_modified(state.file_path, ctx, file_baseline_warnings=state.stats.baseline_warnings):
        state.current_lines.clear()
        state.current_lines.extend(new_lines)
        state.stats.tally.using.removed += len(candidates)
        if state.verbose:
            emit(f"    -- bulk-removed {len(candidates)} using-names: {', '.join(candidates)}")
        return True
    _ = state.file_path.write_text("".join(snapshot), encoding="utf-8")
    return False


def _live_using_block(
    state: BisectState, module_path: str, candidates: list[str]
) -> tuple[ImportBlock, list[str]] | None:
    """Re-find module_path's block and keep only ``candidates`` still present.

    Returns ``(block, present_candidates)`` or None when the block is gone or no
    candidate survives — letting the bisect helper collapse its guard branches.
    """
    fresh = find_live_block(state.current_lines, module_path, 0)
    if fresh is None:
        return None
    present = [n for n in candidates if n in fresh.using_names]
    if not present:
        return None
    return fresh, present


def _bisect_helper_using(
    state: BisectState,
    ctx: TypecheckCtx,
    module_path: str,
    candidates: list[str],
) -> list[str]:
    """Recurse the bisection on ``candidates`` (names in module_path's using clause)."""
    live = _live_using_block(state, module_path, candidates)
    if live is None:
        return []
    fresh, candidates = live

    bulk = _try_bulk_remove_using(state, ctx, fresh, candidates)
    if bulk is None:
        # Couldn't construct the bulk-removal block; bail to per-name on this segment.
        return _bisect_per_name_fallback(state, ctx, module_path, candidates)
    if bulk:
        return candidates
    if len(candidates) == 1:
        if state.verbose:
            emit(f"    -- KEPT {candidates[0]} (live)")
        return []

    mid = len(candidates) // 2
    left_dead = _bisect_helper_using(state, ctx, module_path, candidates[:mid])
    right_dead = _bisect_helper_using(state, ctx, module_path, candidates[mid:])
    return left_dead + right_dead


def _bisect_per_name_fallback(
    state: BisectState,
    ctx: TypecheckCtx,
    module_path: str,
    candidates: list[str],
) -> list[str]:
    """Remove a list of using names in module_path one at a time."""
    removed: list[str] = []
    for name in candidates:
        fresh = find_live_block(state.current_lines, module_path, 0)
        if fresh is None or name not in fresh.using_names:
            continue
        if _try_remove_using(state, ctx, fresh, name):
            removed.append(name)
    return removed


def _try_remove_using(
    state: BisectState,
    ctx: TypecheckCtx,
    block: ImportBlock,
    name: str,
) -> bool:
    """Try removing a single using-name.  Returns True if removed."""
    snapshot = list(state.current_lines)
    new_raw = remove_name_from_raw(block.raw, name)
    if new_raw is None:
        return False
    new_lines = replace_block_in_lines(state.current_lines, block, new_raw)
    _ = state.file_path.write_text("".join(new_lines), encoding="utf-8")
    state.stats.tally.type_checks += 1
    state.stats.tally.using.tested += 1
    if check_modified(state.file_path, ctx, file_baseline_warnings=state.stats.baseline_warnings):
        state.current_lines.clear()
        state.current_lines.extend(new_lines)
        state.stats.tally.using.removed += 1
        if state.verbose:
            emit(f"    -- removed using-name `{name}` from `{block.module_path}`")
        return True
    _ = state.file_path.write_text("".join(snapshot), encoding="utf-8")
    if state.verbose:
        emit(f"    -- KEPT using-name `{name}` from `{block.module_path}` (live)")
    return False


def _bisect_renaming(
    state: BisectState, ctx: TypecheckCtx, block: ImportBlock
) -> list[tuple[str, str]]:
    """Bisect on renaming pairs.  Symmetric to ``_bisect_using``."""
    return _bisect_helper_renaming(state, ctx, block.module_path, list(block.renaming_pairs))


def _try_bulk_remove_renaming(
    state: BisectState,
    ctx: TypecheckCtx,
    fresh: ImportBlock,
    candidates: list[tuple[str, str]],
) -> bool | None:
    """Attempt to drop ALL ``candidates`` from ``fresh`` in one type-check.

    Returns True if every candidate is dead (changes accepted), False if the
    bulk removal does not type-check (file restored), or None if the bulk-removed
    block text could not even be constructed (caller falls back to per-pair).
    """
    new_raw: str | None = fresh.raw
    for src, dst in candidates:
        nxt = remove_rename_from_raw(new_raw, src, dst)
        if nxt is None:
            return None
        new_raw = nxt

    snapshot = list(state.current_lines)
    new_lines = replace_block_in_lines(state.current_lines, fresh, new_raw)
    _ = state.file_path.write_text("".join(new_lines), encoding="utf-8")
    state.stats.tally.type_checks += 1
    state.stats.tally.renaming.tested += len(candidates)
    if check_modified(state.file_path, ctx, file_baseline_warnings=state.stats.baseline_warnings):
        state.current_lines.clear()
        state.current_lines.extend(new_lines)
        state.stats.tally.renaming.removed += len(candidates)
        if state.verbose:
            emit(f"    -- bulk-removed {len(candidates)} renaming-pairs")
        return True
    _ = state.file_path.write_text("".join(snapshot), encoding="utf-8")
    return False


def _live_renaming_block(
    state: BisectState, module_path: str, candidates: list[tuple[str, str]]
) -> tuple[ImportBlock, list[tuple[str, str]]] | None:
    """Re-find module_path's block and keep only ``candidates`` still present.

    Returns ``(block, present_candidates)`` or None when the block is gone or no
    pair survives — letting the bisect helper collapse its guard branches.
    """
    fresh = find_live_block(state.current_lines, module_path, 0)
    if fresh is None:
        return None
    present = [p for p in candidates if p in fresh.renaming_pairs]
    if not present:
        return None
    return fresh, present


def _bisect_helper_renaming(
    state: BisectState,
    ctx: TypecheckCtx,
    module_path: str,
    candidates: list[tuple[str, str]],
) -> list[tuple[str, str]]:
    """Recurse the bisection on renaming-pair ``candidates`` in module_path."""
    live = _live_renaming_block(state, module_path, candidates)
    if live is None:
        return []
    fresh, candidates = live

    bulk = _try_bulk_remove_renaming(state, ctx, fresh, candidates)
    if bulk is None:
        return _bisect_per_pair_fallback(state, ctx, module_path, candidates)
    if bulk:
        return candidates
    if len(candidates) == 1:
        return []

    mid = len(candidates) // 2
    return _bisect_helper_renaming(
        state, ctx, module_path, candidates[:mid]
    ) + _bisect_helper_renaming(state, ctx, module_path, candidates[mid:])


def _bisect_per_pair_fallback(
    state: BisectState,
    ctx: TypecheckCtx,
    module_path: str,
    candidates: list[tuple[str, str]],
) -> list[tuple[str, str]]:
    """Remove a list of renaming pairs in module_path one at a time."""
    removed: list[tuple[str, str]] = []
    for src, dst in candidates:
        fresh = find_live_block(state.current_lines, module_path, 0)
        if fresh is None or (src, dst) not in fresh.renaming_pairs:
            continue
        if _try_remove_renaming(state, ctx, fresh, src, dst):
            removed.append((src, dst))
    return removed


def _try_remove_renaming(
    state: BisectState,
    ctx: TypecheckCtx,
    block: ImportBlock,
    src: str,
    dst: str,
) -> bool:
    """Try removing a single renaming pair.  Returns True if removed."""
    snapshot = list(state.current_lines)
    new_raw = remove_rename_from_raw(block.raw, src, dst)
    if new_raw is None:
        return False
    new_lines = replace_block_in_lines(state.current_lines, block, new_raw)
    _ = state.file_path.write_text("".join(new_lines), encoding="utf-8")
    state.stats.tally.type_checks += 1
    state.stats.tally.renaming.tested += 1
    if check_modified(state.file_path, ctx, file_baseline_warnings=state.stats.baseline_warnings):
        state.current_lines.clear()
        state.current_lines.extend(new_lines)
        state.stats.tally.renaming.removed += 1
        if state.verbose:
            emit(f"    -- removed renaming-pair `{src} to {dst}` from `{block.module_path}`")
        return True
    _ = state.file_path.write_text("".join(snapshot), encoding="utf-8")
    if state.verbose:
        emit(f"    -- KEPT renaming-pair `{src} to {dst}` (live)")
    return False


# ----------------------------------------------------------------------------
# CLI / orchestration
# ----------------------------------------------------------------------------


def worker_process_file(args: tuple[Path, PruneConfig]) -> FileStats:
    """Run ``prune_file`` for one (file, config) pair (process-pool entry point)."""
    file_path, config = args
    return prune_file(file_path, config)


def _build_arg_parser() -> argparse.ArgumentParser:
    """Construct the argument parser for the prune CLI."""
    parser = argparse.ArgumentParser(
        formatter_class=argparse.RawDescriptionHelpFormatter,
        description=__doc__,
    )
    parser.add_argument(
        "paths", nargs="*", type=Path, help="Files or directories to prune (default: src/)"
    )
    parser.add_argument(
        "-j", "--workers", type=int, default=4, help="Parallel file workers (default: 4)"
    )
    parser.add_argument(
        "--rts-cores", type=int, default=8, help="GHC RTS cores per agda call (default: 8)"
    )
    parser.add_argument(
        "--rts-heap", type=int, default=3, help="GHC RTS heap per agda call in GB (default: 3)"
    )
    parser.add_argument(
        "--timeout", type=int, default=300, help="Per-agda-call timeout seconds (default: 300)"
    )
    parser.add_argument(
        "--include-public", action="store_true", help="Test `public` re-export lines too"
    )
    parser.add_argument(
        "--final-check",
        action="store_true",
        help="Run cabal run shake -- check-properties after pruning",
    )
    parser.add_argument(
        "--dry-run", action="store_true", help="Don't write changes; report what would be removed"
    )
    parser.add_argument("--quiet", action="store_true", help="Suppress per-file output")
    parser.add_argument("--verbose", action="store_true", help="Per-name decision logging")
    parser.add_argument(
        "--no-bisect", action="store_true", help="Disable bisection (pure per-name brute force)"
    )
    parser.add_argument(
        "--no-topo",
        action="store_true",
        help=(
            "Hint: skip topological-level batching IF the input set has no "
            + "inter-dependencies (single topo level).  Saves the topo-graph startup "
            + "cost for small independent subsets.  If inter-deps are detected, the "
            + "tool auto-enables topo batching (since `--no-topo` + multi-worker on "
            + "inter-deps reliably races on `.agdai` writes).  Pass `--workers 1` to "
            + "force pure sequential without topo cost."
        ),
    )
    parser.add_argument(
        "--check-only",
        action="store_true",
        help=(
            "Lint-mode: implies --dry-run + --quiet; exits 1 if any dead imports "
            + "would be removed, 0 if clean.  Intended for CI gates / pre-commit / "
            + "pre-push hooks."
        ),
    )
    parser.add_argument(
        "--restore-backups",
        action="store_true",
        help="Restore any *.prune-bak files left by an interrupted run, then exit",
    )
    return parser


Batch = list[tuple[Path, PruneConfig]]


def _build_consumers_map(*, include_public: bool, quiet: bool) -> dict[str, list[Path]]:
    """Build the module-name -> importers graph when ``--include-public`` is set.

    Always scans the full ``src/`` tree (not just the requested paths) — a file
    in the requested set may have consumers elsewhere.  Returns an empty mapping
    when ``include_public`` is off (no consumer checks are needed then).
    """
    if not include_public:
        return {}
    if not quiet:
        emit("  building reverse dependency graph (full src/ tree)...")
    consumers_map = build_reverse_dep_graph(gather_agda_files([SRC_DIR]))
    if not quiet:
        edges = sum(len(v) for v in consumers_map.values())
        emit(f"  reverse graph: {len(consumers_map)} modules indexed, {edges} consumer edges")
    return consumers_map


def _plan_batches(files: list[Path], config: PruneConfig, args: argparse.Namespace) -> list[Batch]:
    """Group ``(file, config)`` work items into race-free execution batches.

    Topo batching is ON by default: parallel workers on inter-dependent files
    race on ``.agdai`` writes.  ``--no-topo`` is a HINT honoured only when the
    input has no inter-dependencies (a single topo level); otherwise the tool
    auto-overrides to topo batching to keep the race-free guarantee.
    ``--workers 1`` forces a single sequential bucket (no race).
    """
    worker_args: Batch = [(f, config) for f in files]
    if args.workers <= 1:
        return [worker_args]  # serial — no race

    levels = topological_levels(files, SRC_DIR)
    if args.no_topo:
        if len(levels) <= 1:
            return [worker_args]
        if not args.quiet:
            emit(
                "  --no-topo overridden: input has inter-dependent files "
                + f"({len(levels)} topo levels); using topo batching to avoid .agdai "
                + "race (feedback_agda_import_pruning_safety.md).  Pass `--workers 1` "
                + "for sequential without topo cost."
            )
    wa_by_file = {item[0]: item for item in worker_args}
    batches = [[wa_by_file[f] for f in level if f in wa_by_file] for level in levels]
    if not args.no_topo and not args.quiet:
        sizes = [len(b) for b in batches[:_BATCH_PREVIEW_LIMIT]]
        tail = "..." if len(batches) > _BATCH_PREVIEW_LIMIT else ""
        emit(f"  topological-level batching: {len(batches)} levels (sizes: {sizes}{tail})")
    return batches


def _execute_batches(batches: list[Batch], args: argparse.Namespace) -> list[FileStats]:
    """Run the planned batches and collect per-file stats.

    Serial when ``--workers <= 1``; otherwise a fresh ``ProcessPoolExecutor`` per
    level (files within a level have no inter-dependencies, so are race-free).
    """
    all_stats: list[FileStats] = []

    def consume(stats: FileStats) -> None:
        all_stats.append(stats)
        _print_stats(stats, quiet=args.quiet)

    if args.workers <= 1:
        for item in batches[0]:
            consume(worker_process_file(item))
        return all_stats

    for level_idx, batch in enumerate(batches):
        if not batch:
            continue
        if not args.quiet and len(batches) > 1:
            emit(f"  >>> level {level_idx} ({len(batch)} files)")
        with concurrent.futures.ProcessPoolExecutor(
            max_workers=min(args.workers, len(batch))
        ) as pool:
            futures = {pool.submit(worker_process_file, item): item[0] for item in batch}
            for fut in concurrent.futures.as_completed(futures):
                consume(fut.result())
    return all_stats


def _print_run_summary(all_stats: list[FileStats], elapsed: float, *, dry_run: bool) -> None:
    """Print the aggregate post-run summary block."""
    total_removed = sum(s.removed_total for s in all_stats)
    files_changed = sum(1 for s in all_stats if s.removed_total > 0)
    using = sum(s.tally.using.removed for s in all_stats)
    renaming = sum(s.tally.renaming.removed for s in all_stats)
    emit()
    emit("=== summary ===")
    emit(f"  files processed: {len(all_stats)}")
    emit(f"  files modified : {files_changed}")
    emit(f"  dead names removed: {total_removed} (using: {using}, renaming: {renaming})")
    emit(f"  public blocks skipped: {sum(s.tally.public_blocks_skipped for s in all_stats)}")
    emit(f"  type-checks run: {sum(s.tally.type_checks for s in all_stats)}")
    emit(f"  errors: {sum(1 for s in all_stats if s.error)}")
    emit(f"  wall time: {elapsed:.1f}s")
    if dry_run:
        emit("  (dry-run: no files modified)")


def main() -> int:
    """Parse arguments, prune (or check) the requested files, and return the exit code."""
    args = _build_arg_parser().parse_args()

    if args.restore_backups:
        paths = args.paths if args.paths else [SRC_DIR]
        emit(f"restored {restore_backups(paths)} backup(s)")
        return 0

    # --check-only implies --dry-run + --quiet (lint mode for CI/hooks).
    if args.check_only:
        args.dry_run = True
        args.quiet = True

    paths = args.paths if args.paths else [SRC_DIR]

    # Crash-safe cleanup: sweep any leftovers from a prior interrupted run
    # (e.g. a SIGKILL that bypassed the signal handler), then arm exit/signal
    # restore for THIS run so an interruption never leaves the tree corrupted.
    swept = _cleanup_stray_backups()
    if swept and not args.quiet:
        emit(f"start sweep: restored {swept} file(s) left modified by a prior interrupted run")
    _install_cleanup_handlers()
    files = gather_agda_files(paths)
    if not files:
        _ = sys.stderr.write("error: no .agda files found\n")
        return 1

    consumers_map = _build_consumers_map(include_public=args.include_public, quiet=args.quiet)
    config = PruneConfig(
        ctx=TypecheckCtx(
            src_dir=SRC_DIR,
            rts_cores=args.rts_cores,
            rts_heap_gb=args.rts_heap,
            timeout=args.timeout,
        ),
        include_public=args.include_public,
        dry_run=args.dry_run,
        use_bisect=not args.no_bisect,
        verbose=args.verbose,
        consumers_map=consumers_map,
    )

    if not args.quiet:
        emit(f"prune_unused_imports: processing {len(files)} files with {args.workers} workers")
        emit(
            f"  src_dir={SRC_DIR}, rts={args.rts_cores}c/{args.rts_heap}G, "
            + f"timeout={args.timeout}s, include_public={args.include_public}, "
            + f"dry_run={args.dry_run}, bisect={not args.no_bisect}"
        )

    t_start = time.monotonic()
    batches = _plan_batches(files, config, args)
    all_stats = _execute_batches(batches, args)
    elapsed = time.monotonic() - t_start

    _print_run_summary(all_stats, elapsed, dry_run=args.dry_run)
    return _final_exit_code(all_stats, args)


def _final_exit_code(all_stats: list[FileStats], args: argparse.Namespace) -> int:
    """Run the optional final check and map the run outcome to an exit code.

    Exit-code semantics:
      0 — tool ran successfully AND (apply mode OR dry-run found no dead).
      1 — tool/agda errors during the run (baseline failures, exceptions), OR
          ``--dry-run`` / ``--check-only`` found dead imports (matches
          gofmt -l / prettier --check / eslint / pyflakes — the universal
          lint-tool convention).
      2 — ``--final-check`` failed in apply mode.
    """
    if args.final_check and not args.dry_run:
        emit()
        emit("=== final project-wide check-properties ===")
        if not project_typecheck():
            _ = sys.stderr.write("  FAIL — project-wide check-properties broke after pruning!\n")
            return 2
        emit("  PASS")

    if any(s.error for s in all_stats):
        return 1
    total_removed = sum(s.removed_total for s in all_stats)
    if args.dry_run and total_removed > 0:
        if args.check_only:
            # --check-only suppresses verbose output; surface the count here
            # so CI logs and pre-commit hooks have a one-line failure signal.
            files_changed = sum(1 for s in all_stats if s.removed_total > 0)
            _ = sys.stderr.write(
                f"prune_unused_imports: {total_removed} dead name(s) found across "
                + f"{files_changed} file(s); run without --check-only to remove\n"
            )
        return 1
    return 0


def _print_stats(stats: FileStats, *, quiet: bool) -> None:
    """Print one file's per-file result line (skipped when quiet and uneventful)."""
    if quiet and not stats.error and stats.removed_total == 0:
        return
    try:
        rel = stats.file.relative_to(REPO_ROOT)
    except ValueError:
        rel = stats.file
    if stats.error:
        emit(f"  {rel}  ERROR: {stats.error}")
        return
    skipped = stats.tally.public_blocks_skipped
    public = f"public-skipped={skipped}" if skipped else ""
    emit(
        f"  {rel}  removed={stats.removed_total} "
        + f"(using {stats.tally.using.removed}/{stats.tally.using.tested}, "
        + f"renaming {stats.tally.renaming.removed}/{stats.tally.renaming.tested}) "
        + f"tcs={stats.tally.type_checks} t={stats.seconds:.1f}s {public}"
    )


if __name__ == "__main__":
    sys.exit(main())
