#!/usr/bin/env python3
# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
"""Driver + equivalence check for the scope-aware `.agdai` IWYU reader (Route A).

Builds `tools/agda-iwyu-reader` on demand (linking the PREBUILT Agda from the
cabal store, never a fresh solve), turns each dead-import candidate into a
`(module, name)` query, runs the reader, and compares its USED/DEAD verdict
against the recompile-confirm ORACLE
(:func:`tools.warm_dead_imports.process_names`).

The ONE release-blocking disagreement is a **false negative**: the reader says
DEAD but removing the import fails to type-check (the oracle keeps it).  The
reverse — reader keeps / UNRESOLVED while the oracle finds it removable — is the
safe direction (an over-keep, or the IWYU-vs-brute-force distinction), reported
but non-blocking.  `--validate` exits 1 iff any false negative is found; that
clean differential, on a real corpus, is what would license retiring the oracle.

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
from typing import cast

from tools._agda_opens import find_opens
from tools._common import emit, find_executable, run_capture
from tools.prune_unused_imports import AGDA_BIN, SRC_DIR
from tools.warm_dead_imports import (
    SweepResult,
    WarmAgda,
    process_names,
    run_warm_tool,
)

SRC = SRC_DIR
REPO = SRC.parent
AGDA = str(AGDA_BIN)
PKG = Path(__file__).resolve().parent / "agda-iwyu-reader"

# A candidate name -> the (module, original-name) queries that resolve it.  For a
# `using (n)` the query name is n; for `renaming (src to dst)` the candidate is
# dst but the query name is src (the elaborated term references the origin).
type QueryMap = dict[str, list[tuple[str, str]]]
# Reader verdict per (rel, module, query-name).
type Verdicts = dict[tuple[str, str, str], str]


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
            "-package",
            "containers",
            "-package",
            "unordered-containers",
            "-XPatternSynonyms",
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


def candidate_queries(text: str) -> QueryMap:
    """Map each prunable import name to its ``(module, original-name)`` queries.

    Mirrors the gate's candidate set (:func:`tools._agda_opens.open_check_names`)
    but keeps the module + original-name association the reader needs.  A
    ``using (n)`` entry resolves as ``(module, n)`` (a ``module `` prefix
    stripped); a ``renaming (src to dst)`` candidate ``dst`` resolves as
    ``(module, src)`` — the elaborated term references the origin, never the alias.
    """
    qmap: QueryMap = {}
    for open_info in find_opens(text):
        is_candidate = (
            open_info.is_open
            and (open_info.has_using or bool(open_info.renaming))
            and not open_info.has_public
        )
        if not is_candidate:
            continue
        for raw in open_info.using_names:
            name = raw[len("module ") :].strip() if raw.startswith("module ") else raw
            qmap.setdefault(name, []).append((open_info.module, name))
        for src, dst in open_info.renaming:
            qmap.setdefault(dst, []).append((open_info.module, src))
    return qmap


def _decode_verdict(line: str, by_path: dict[str, str]) -> tuple[tuple[str, str, str], str] | None:
    """Decode one reader JSONL line into ((rel, mod, name), verdict), or None."""
    line = line.strip()
    if not line.startswith("{"):
        return None
    raw = cast("object", json.loads(line))
    if not isinstance(raw, dict):
        return None
    obj = cast("dict[str, object]", raw)
    path, mod, name, verdict = obj.get("path"), obj.get("mod"), obj.get("name"), obj.get("verdict")
    if not all(isinstance(v, str) for v in (path, mod, name, verdict)):
        return None
    rel = by_path.get(cast("str", path))
    if rel is None:
        return None
    return (rel, cast("str", mod), cast("str", name)), cast("str", verdict)


def run_reader(queries: list[tuple[str, str, str]]) -> Verdicts:
    """Run the reader over ``(rel, module, name)`` queries; map each to its verdict.

    Only queries whose file has a present `.agdai` are sent (the caller treats a
    missing verdict as "reader could not judge" → defer to the oracle).
    """
    if not queries:
        return {}
    binary = build_reader()
    rels = {rel for rel, _mod, _name in queries}
    present = {rel: _agdai_path(rel) for rel in rels if _agdai_path(rel).is_file()}
    by_path = {str(p): rel for rel, p in present.items()}
    lines = [f"{present[rel]}\t{mod}\t{name}" for rel, mod, name in queries if rel in present]
    if not lines:
        return {}
    env = {**os.environ, "AGDA_IWYU_INCLUDE_PATHS": ":".join(_include_paths())}
    result = subprocess.run(
        [str(binary)],
        input="\n".join(lines) + "\n",
        capture_output=True,
        text=True,
        env=env,
        check=False,
    )
    verdicts: Verdicts = {}
    for line in result.stdout.splitlines():
        decoded = _decode_verdict(line, by_path)
        if decoded is not None:
            verdicts[decoded[0]] = decoded[1]
    return verdicts


def _reader_verdict(rel: str, name: str, qmap: QueryMap, verdicts: Verdicts) -> str:
    """Aggregate a candidate's reader verdict across its ``(module, name)`` queries.

    USED if any query is USED; DEAD only if all are DEAD; otherwise UNRESOLVED
    (a missing or UNRESOLVED query → defer to the oracle, never DEAD).
    """
    qs = qmap.get(name, [])
    results = [verdicts.get((rel, mod, orig)) for mod, orig in qs]
    if not results or any(r is None for r in results):
        return "UNRESOLVED"
    if "USED" in results:
        return "USED"
    if all(r == "DEAD" for r in results):
        return "DEAD"
    return "UNRESOLVED"


def _classify_file(
    rel: str,
    cands: list[str],
    qmap: QueryMap,
    verdicts: Verdicts,
    dead_set: set[str],
) -> tuple[int, int, int]:
    """Compare reader vs oracle per candidate; return (false_negs, over_keeps, agree).

    A FALSE NEGATIVE (reader DEAD, oracle ALIVE) is the only blocking direction;
    the reverse (reader keeps / UNRESOLVED, oracle DEAD) is a safe over-keep.
    """
    false_negs = over_keeps = agree = 0
    for name in cands:
        reader = _reader_verdict(rel, name, qmap, verdicts)
        oracle = "DEAD" if name in dead_set else "ALIVE"
        if reader == "DEAD" and oracle == "ALIVE":
            emit(f"  ✗ FALSE NEGATIVE {rel}: {name}  reader=DEAD oracle=ALIVE")
            false_negs += 1
        elif reader != "DEAD" and oracle == "DEAD":
            emit(f"  · over-keep {rel}: {name}  reader={reader} oracle=DEAD (safe)")
            over_keeps += 1
        else:
            agree += 1
    return false_negs, over_keeps, agree


def _validate(agda: WarmAgda, swept: SweepResult) -> int:
    """Differential: reader verdict vs recompile-confirm oracle over the candidates.

    For every sieve candidate, the reader's aggregated verdict is compared with
    the oracle's (remove-one + recompile).  Reports the blocking direction —
    reader DEAD yet the oracle keeps it (a false negative) — plus the safe
    over-keep direction; exits 1 iff any false negative is found.
    """
    qmaps = {
        rel: candidate_queries((SRC / rel).read_text(encoding="utf-8")) for rel in swept.candidates
    }
    queries = [
        (rel, mod, orig)
        for rel, cands in swept.candidates.items()
        for name in cands
        for mod, orig in qmaps[rel].get(name, [])
    ]
    verdicts = run_reader(queries)
    false_negs = over_keeps = agree = 0
    for rel, cands in swept.candidates.items():
        oracle_dead, _alive = process_names(agda, rel, cands, keep=False)
        fneg, over, ag = _classify_file(rel, cands, qmaps[rel], verdicts, set(oracle_dead))
        false_negs += fneg
        over_keeps += over
        agree += ag
    emit(
        f"=== reader-vs-oracle: {false_negs} FALSE NEGATIVE(s), "
        + f"{over_keeps} over-keep, {agree} agree ==="
    )
    return 1 if false_negs else 0


def main() -> int:
    """Run the reader-vs-oracle differential over the scoped files; exit 1 on any FN.

    Scope flags mirror the dead-import gate (`--all` / `--diff` / explicit paths),
    resolved by the shared `run_warm_tool` shell; `--validate` is accepted and
    ignored (this tool only validates for now).
    """
    args = [a for a in sys.argv[1:] if a != "--validate"]
    return run_warm_tool(args, _validate)


if __name__ == "__main__":
    sys.exit(main())
