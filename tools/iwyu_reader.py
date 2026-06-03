#!/usr/bin/env python3
# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
"""Driver for the `.agdai` IWYU reader (Route A) + its equivalence check.

Builds `tools/agda-iwyu-reader` on demand (linking the PREBUILT Agda from the
cabal store, never a fresh solve), runs it over the scoped modules' interface
files, and turns its elaboration-complete used-QName set into a dead-import
verdict by matching the reader's used def-sites against the sieve's import
def-ids (the `(file, position)` coordinate).

`--validate` compares the reader's dead-set against the recompile-confirm ORACLE
(:func:`tools.warm_dead_imports.process_names`) restricted to the sieve's
candidates.  Equivalence is what would license retiring recompile-confirm for
the (one-typecheck) reader.

KNOWN GAP (surfaced by --validate, 2026-06-04): the `(file, position)` def-id
agrees with the highlighting only for DIRECTLY-defined names.  It does NOT for
(a) RE-EXPORTS — highlighting points the import at the re-export site, the reader
at the canonical definition (e.g. `[]`: `Data/List/Base.agda` vs
`prim/.../Builtin/List.agda`); and (b) MODULE imports — a module is not a
term-level QName, so `namesIn` never holds it (only its contents).  Both make the
naive def-id match over-report dead.  The fix is scope-aware resolution: resolve
each imported name to its canonical QName via the interface's `iInsideScope`
(handles re-exports precisely) and treat a module import as used iff some of its
contents are used.  Until then `--validate` reports these as mismatches.

Invoke: `python -m tools.iwyu_reader --validate (--all | --diff | FILE.agda ...)`.
"""

from __future__ import annotations

import functools
import json
import os
import subprocess
import sys
import tempfile
from pathlib import Path
from typing import NamedTuple, cast

from tools._common import emit, find_executable, run_capture
from tools.prune_unused_imports import AGDA_BIN, SRC_DIR
from tools.warm_dead_imports import (
    DefId,
    LoadResult,
    SweepResult,
    WarmAgda,
    detect_dead,
    import_defids,
    process_names,
    run_warm_tool,
)

SRC = SRC_DIR
REPO = SRC.parent
AGDA = str(AGDA_BIN)
PKG = Path(__file__).resolve().parent / "agda-iwyu-reader"

# Used QNames per file, as the (def-file, def-position) coordinate shared with the
# sieve's import def-ids.
type UsedByRel = dict[str, set[DefId]]


class _Parsed(NamedTuple):
    """One reader JSONL line decoded: the module's rel path + its used def-ids."""

    rel: str
    defids: set[DefId]


@functools.cache
def _agda_version() -> str:
    """Numeric Agda version (e.g. ``2.8.0``) — names the `_build/<ver>/` tree."""
    return run_capture([AGDA, "--numeric-version"], check=True).stdout.strip()


def _store_package_db() -> Path:
    """Path to the cabal store package.db holding the prebuilt Agda library."""
    ghc = find_executable("ghc")
    ghc_version = run_capture([ghc, "--numeric-version"], check=True).stdout.strip()
    return Path.home() / ".cabal" / "store" / f"ghc-{ghc_version}" / "package.db"


def build_reader() -> Path:
    """Build (if stale) and return the reader binary, linking the store's Agda.

    A plain `cabal build` re-solves and rebuilds Agda (~15 min); this points ghc
    at the store package.db so the prebuilt library is linked directly.  Rebuilds
    only when the binary is missing or older than `Main.hs`.
    """
    binary, source = PKG / "agda-iwyu-reader", PKG / "Main.hs"
    if binary.is_file() and binary.stat().st_mtime >= source.stat().st_mtime:
        return binary
    db = _store_package_db()
    if not db.exists():
        message = f"cabal store package.db not found: {db} (is Agda cabal-installed?)"
        raise FileNotFoundError(message)
    outdir = Path(tempfile.gettempdir()) / "agda-iwyu-build"
    outdir.mkdir(exist_ok=True)
    result = run_capture(
        [
            find_executable("ghc"),
            "-package-db",
            str(db),
            "-package",
            "Agda",
            "-outputdir",
            str(outdir),
            str(source),
            "-o",
            str(binary),
        ],
        cwd=PKG,
    )
    if result.returncode != 0:
        emit(result.stdout)
        emit(result.stderr)
        message = "agda-iwyu-reader build failed"
        raise RuntimeError(message)
    return binary


def _agdai_path(rel: str) -> Path:
    """Interface file for a src-relative module, under `_build/<ver>/agda/src/`."""
    return REPO / "_build" / _agda_version() / "agda" / "src" / Path(rel).with_suffix(".agdai")


def _lib_includes(libfile: Path) -> list[str]:
    """Absolute include dirs declared by an `.agda-lib` (resolved against its dir)."""
    base = libfile.parent
    includes: list[str] = []
    for raw in libfile.read_text(encoding="utf-8").splitlines():
        line = raw.split("--", 1)[0].strip()
        if line.startswith("include:"):
            parts = line[len("include:") :].split()
            includes.extend(str((base / part).resolve()) for part in parts)
    return includes or [str(base)]


@functools.cache
def _include_paths() -> tuple[str, ...]:
    """Include dirs the reader needs to decode interfaces: project `src` + libraries.

    Must match what wrote the interface, or `decode` fails (it resolves
    module<->source via the include dirs).  Project `src` is `SRC` (the
    `aletheia.agda-lib` `include: src`); library dirs come from `~/.agda/libraries`.
    """
    paths = [str(SRC)]
    libraries = Path.home() / ".agda" / "libraries"
    if libraries.is_file():
        for raw in libraries.read_text(encoding="utf-8").splitlines():
            entry = raw.split("--", 1)[0].strip()
            libfile = Path(entry).expanduser()
            if entry and libfile.is_file():
                paths.extend(_lib_includes(libfile))
    return tuple(paths)


def _used_defids(entries: object) -> set[DefId]:
    """Collect (def-file, def-pos) pairs from a reader entry's ``used`` array."""
    defids: set[DefId] = set()
    if isinstance(entries, list):
        for entry in cast("list[object]", entries):
            if isinstance(entry, dict):
                item = cast("dict[str, object]", entry)
                f, p = item.get("f"), item.get("p")
                if isinstance(f, str) and isinstance(p, int):
                    defids.add((f, p))
    return defids


def _parse_used(line: str, by_path: dict[str, str]) -> _Parsed | None:
    """Parse one reader JSONL line into its rel + used-def-ids, or None to skip it.

    Skips non-object lines, unknown paths, and error objects (a file the reader
    could not decode is left out of the validation rather than mis-flagged).
    """
    line = line.strip()
    if not line.startswith("{"):
        return None
    raw: object = json.loads(line)
    if not isinstance(raw, dict):
        return None
    obj = cast("dict[str, object]", raw)
    path = obj.get("path")
    rel = by_path.get(path) if isinstance(path, str) else None
    if rel is None or "error" in obj:
        return None
    return _Parsed(rel, _used_defids(obj.get("used")))


def run_reader(rels: list[str]) -> UsedByRel:
    """Run the reader over the scoped modules' interfaces; map rel -> used def-ids.

    Only files whose `.agdai` exists and decodes appear in the result (the caller
    skips the rest rather than treating "unread" as "everything dead").
    """
    binary = build_reader()
    present = {rel: _agdai_path(rel) for rel in rels if _agdai_path(rel).is_file()}
    if not present:
        return {}
    by_path = {str(p): rel for rel, p in present.items()}
    env = {**os.environ, "AGDA_IWYU_INCLUDE_PATHS": ":".join(_include_paths())}
    result = subprocess.run(
        [str(binary), *by_path],
        capture_output=True,
        text=True,
        env=env,
        check=False,
    )
    used: UsedByRel = {}
    for line in result.stdout.splitlines():
        parsed = _parse_used(line, by_path)
        if parsed is not None:
            used[parsed.rel] = parsed.defids
    return used


def _check_file(agda: WarmAgda, rel: str, loaded: LoadResult, reader_used: set[DefId]) -> bool:
    """Compare the reader's dead-set against the recompile-confirm oracle for `rel`.

    Returns True on disagreement (a mismatch).  The reader-dead set is the sieve
    candidates whose def-id the reader's used-set lacks; the oracle confirms the
    same candidates by remove-and-recompile.  Files with no candidates agree
    trivially and are silent.
    """
    text = (SRC / rel).read_text(encoding="utf-8")
    abspath = str(SRC / rel)
    candidates = detect_dead(text, loaded.tokens, abspath)["candidates"]
    if not candidates:
        return False
    defids = import_defids(text, loaded.tokens, abspath)
    reader_dead = sorted(c for c in candidates if defids[c] not in reader_used)
    confirmed = sorted(process_names(agda, rel, candidates, keep=False)[0])
    if reader_dead != confirmed:
        emit(f"  MISMATCH {rel}: reader={reader_dead} oracle={confirmed} candidates={candidates}")
        return True
    emit(f"  ok {rel}: dead={confirmed or '—'} (filtered {len(candidates) - len(confirmed)} FP)")
    return False


def _validate(agda: WarmAgda, swept: SweepResult) -> int:
    """Compare reader-dead vs the recompile-confirm oracle over the swept candidates.

    Only files the sieve flagged candidates for can disagree (reader-dead is a
    subset of the sieve candidates); files with none agree trivially.  The sweep
    already refreshed every `.agdai`, so the reader sees interfaces consistent
    with the loaded tokens.  Exit 1 on any disagreement.
    """
    rels = sorted(swept.candidates)
    used = run_reader(rels)
    mismatches = 0
    for rel in rels:
        if rel not in used:
            emit(f"  skip {rel}: reader could not read its .agdai")
            continue
        loaded = agda.load(str(SRC / rel))
        mismatches += int(_check_file(agda, rel, loaded, used[rel]))
    emit(f"=== reader-vs-oracle: {mismatches} mismatch(es) ===")
    return 1 if mismatches else 0


def main() -> int:
    """Validate the reader against the recompile-confirm oracle over the scoped files.

    Scope flags mirror the dead-import gate (`--all` / `--diff` / explicit paths),
    resolved by the shared `run_warm_tool` shell; `--validate` is accepted and
    ignored (this tool only validates for now).  Exit 1 if the reader disagrees
    with the oracle on any file.
    """
    args = [a for a in sys.argv[1:] if a != "--validate"]
    return run_warm_tool(args, _validate)


if __name__ == "__main__":
    sys.exit(main())
