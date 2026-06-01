"""Warm-engine driver for the dead-import prune (ci-speed branch).

Runs prune's EXACT algorithm — per-`(block, name)` targeting via `find_live_block`,
bisection, crash-safe `.prune-bak` — but routes every type-check through ONE
persistent agda process (`WarmAgda`) instead of a cold subprocess per check, by
injecting a `WarmCheck` on the `TypecheckCtx`.  So it is FN-complete BY
CONSTRUCTION (it IS prune) yet ~10x faster, and is the warm replacement that lets
the cold prune driver be retired.

Single serial agda process (prune's `-j` parallelism collapses to one warm
process — the amortized stdlib/interface load is the trade).  Invoke:
`python -m tools.warm_prune [--apply] <relpath.agda | dir> [...]`.
A check-only run exits nonzero when any dead import is found.
"""

from __future__ import annotations

import sys
import time
from pathlib import Path
from typing import TYPE_CHECKING

from tools._agda_imports import TypecheckCtx, WarmVerdict, gather_agda_files
from tools._common import emit
from tools.prune_unused_imports import PruneConfig, prune_file
from tools.warm_dead_imports import SRC, WarmAgda, count_semantic_warnings

if TYPE_CHECKING:
    from tools._agda_imports import WarmCheck

# The warm process is configured by _spawn_agda (-M16G -N8); these cold-ctx RTS
# fields are unused when `warm` is set but TypecheckCtx still requires them.
_WARM_CTX_PLACEHOLDER_HEAP_GB = 16
_WARM_CTX_PLACEHOLDER_CORES = 8
_WARM_CTX_PLACEHOLDER_TIMEOUT = 300


def make_warm_check(agda: WarmAgda) -> WarmCheck:
    """Return a WarmCheck that re-loads a file in `agda` and reports its verdict."""

    def warm_check(rel_path: str) -> WarmVerdict:
        result = agda.load(str(SRC / rel_path))
        return WarmVerdict(result.ok, count_semantic_warnings(result.warnings))

    return warm_check


def _resolve_files(args: list[str]) -> list[Path]:
    """Resolve CLI path args (src-relative or absolute) to a sorted .agda file list."""
    roots = [Path(a) if Path(a).is_absolute() else SRC / a for a in args]
    return gather_agda_files(roots)


def main() -> int:
    """Warm-prune the given files/dirs; --apply writes, else check-only (nonzero=dead)."""
    args = sys.argv[1:]
    apply = "--apply" in args
    rels = [a for a in args if not a.startswith("--")]
    files = _resolve_files(rels)
    if not files:
        emit("usage: python -m tools.warm_prune [--apply] <relpath.agda | dir> [...]")
        return 2
    start = time.time()
    n_dead = 0
    with WarmAgda() as agda:
        ctx = TypecheckCtx(
            src_dir=SRC,
            rts_cores=_WARM_CTX_PLACEHOLDER_CORES,
            rts_heap_gb=_WARM_CTX_PLACEHOLDER_HEAP_GB,
            timeout=_WARM_CTX_PLACEHOLDER_TIMEOUT,
            warm=make_warm_check(agda),
        )
        config = PruneConfig(
            ctx=ctx, include_public=False, dry_run=not apply, use_bisect=True, verbose=True
        )
        for f in files:
            stats = prune_file(f, config)
            n_dead += stats.removed_total
            tag = " APPLIED" if apply and stats.removed_total else ""
            err = f"  ERROR={stats.error}" if stats.error else ""
            emit(
                f"{f.relative_to(SRC)}: dead={stats.removed_total}{tag}{err}  "
                + f"({stats.seconds:.1f}s)"
            )
    emit(
        f"=== warm-prune: {n_dead} dead import(s) across {len(files)} file(s) "
        + f"in {time.time() - start:.1f}s ==="
    )
    return 1 if n_dead and not apply else 0


if __name__ == "__main__":
    sys.exit(main())
