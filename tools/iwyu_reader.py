#!/usr/bin/env python3
# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
"""Driver + equivalence check for the scope-aware `.agdai` IWYU reader (Route A).

Builds `tools/agda-iwyu-reader` on demand (linking the PREBUILT Agda from the
cabal store, never a fresh solve), turns each dead-import candidate into a
`NameQuery`, runs the reader, and compares its USED/DEAD verdict against the
recompile-confirm ORACLE (:func:`tools.warm_dead_imports.process_names`).

The ONE release-blocking disagreement is a **false negative**: the reader says
DEAD but removing the import fails to type-check (the oracle keeps it).  The
reverse — reader keeps / UNRESOLVED while the oracle finds it removable — is the
safe direction (an over-keep, or the IWYU-vs-brute-force distinction), reported
but non-blocking.  `--validate` exits 1 iff any false negative is found; that
clean differential, on a real corpus, is what would license retiring the oracle.

Also exposes `read_wildcards` (the USED subset of each wildcard `open import M`)
for the narrowing / redundancy driver :mod:`tools.iwyu_narrow`.

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
from typing import NamedTuple, TypedDict, cast

from tools._agda_opens import ModulePath, find_opens
from tools._common import emit, find_executable, run_capture
from tools.prune_unused_imports import AGDA_BIN, SRC_DIR
from tools.warm_dead_imports import (
    Name,
    RelPath,
    SweepResult,
    WarmAgda,
    process_names,
    run_warm_tool,
)

SRC = SRC_DIR
REPO = SRC.parent
AGDA = str(AGDA_BIN)
PKG = Path(__file__).resolve().parent / "agda-iwyu-reader"

# The filesystem path string of a compiled `.agdai`.
type AgdaiPath = str
# The reader's per-name answer.
type Verdict = str  # one of "USED" | "DEAD" | "UNRESOLVED"
# A tab-separated reader query: "<agdai>\t<module>\t<name>" (name "*" = wildcard).
type QueryLine = str
# A JSONL line the reader writes to stdout (a verdict / wildcard / error object).
type OutputLine = str
# An Agda include directory the reader needs to decode interfaces.
type IncludeDir = str


class ReaderLine(TypedDict, total=False):
    """One JSONL line emitted by `agda-iwyu-reader` (the schema we author there).

    Every line carries `path`/`mod`/`name`; then exactly one of `verdict` (a name
    query), `used` (a wildcard query, `name == "*"`), or `error` (the file could
    not be decoded).  `total=False` because each line sets only its own variant's
    keys, so reads go through `.get`.
    """

    path: AgdaiPath
    mod: ModulePath
    name: Name  # the queried name, or "*" for a wildcard query
    verdict: Verdict
    used: list[Name]
    error: str


def parse_reader_line(line: str) -> ReaderLine | None:
    """Parse one reader JSONL line into a `ReaderLine`, or None if it is not one.

    A line starting with `{` that parses is a JSON object (the schema we author);
    non-`{` lines and malformed JSON both yield None so the read loop can skip them.
    """
    line = line.strip()
    if not line.startswith("{"):
        return None
    try:
        return cast("ReaderLine", json.loads(line))
    except json.JSONDecodeError:
        return None


def verdict_fields(line: str) -> VerdictFields | None:
    """Extract a name-query line's fields, or None if it is not a verdict line.

    Shared by the reader driver (which maps `path`→rel) and the fixture test
    (which maps `path`→consumer stem), so the parse + None-check lives once.
    """
    obj = parse_reader_line(line)
    if obj is None:
        return None
    path, mod, name, verdict = obj.get("path"), obj.get("mod"), obj.get("name"), obj.get("verdict")
    if path is None or mod is None or name is None or verdict is None:
        return None
    return VerdictFields(path, mod, name, verdict)


def wildcard_fields(line: str) -> WildcardFields | None:
    """Extract a wildcard line's fields (`name == "*"`), or None otherwise."""
    obj = parse_reader_line(line)
    if obj is None:
        return None
    path, mod, name, used = obj.get("path"), obj.get("mod"), obj.get("name"), obj.get("used")
    if path is None or mod is None or name != "*" or used is None:
        return None
    return WildcardFields(path, mod, frozenset(used))


class NameQuery(NamedTuple):
    """One import to ask the reader "is this used?" about.

    `rel` is the consumer file; `module` is the module the name is imported from;
    `name` is the name as it appears IN that module — for a `renaming (orig to
    alias)` candidate this is `orig`, since the elaborated term references the
    origin, never the alias.
    """

    rel: RelPath
    module: ModulePath
    name: Name


class WildQuery(NamedTuple):
    """A wildcard `open import module` in consumer file `rel`, asked for its used subset."""

    rel: RelPath
    module: ModulePath


class ImportRef(NamedTuple):
    """A name as brought in by one open: the source `module` and the original `name`."""

    module: ModulePath
    name: Name


class DecodedVerdict(NamedTuple):
    """One parsed reader line: the name query it answers and its verdict."""

    query: NameQuery
    verdict: Verdict


class DecodedWild(NamedTuple):
    """One parsed reader line: the wildcard query it answers and the used subset."""

    query: WildQuery
    used: frozenset[Name]


class VerdictFields(NamedTuple):
    """The raw fields of a reader name-query line (path not yet mapped to a rel)."""

    path: AgdaiPath
    module: ModulePath
    name: Name
    verdict: Verdict


class WildcardFields(NamedTuple):
    """The raw fields of a reader wildcard line (path not yet mapped to a rel)."""

    path: AgdaiPath
    module: ModulePath
    used: frozenset[Name]


class AgdaiFiles(NamedTuple):
    """The present `.agdai` files, in both lookup directions for reader I/O."""

    by_rel: dict[RelPath, Path]  # src-rel → its `.agdai` path (only files that exist)
    rel_by_path: dict[AgdaiPath, RelPath]  # `.agdai` path string → src-rel (maps output back)


# A candidate name -> the import(s) that resolve it within one file (a `using (n)`
# yields ImportRef(M, n); a `renaming (src to dst)` candidate `dst` yields
# ImportRef(M, src)).
type QueryMap = dict[Name, list[ImportRef]]
# Reader verdict per name query.
type Verdicts = dict[NameQuery, Verdict]
# USED subset of a wildcard-opened module's exports, per wildcard query.
type WildUsed = dict[WildQuery, frozenset[Name]]


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


def _agdai_path(rel: RelPath) -> Path:
    """Interface file for a src-relative module, under `_build/<ver>/agda/src/`."""
    return REPO / "_build" / _agda_version() / "agda" / "src" / Path(rel).with_suffix(".agdai")


def _lib_includes(libfile: Path) -> list[IncludeDir]:
    """Absolute include dirs declared by an `.agda-lib` (resolved against its dir)."""
    base = libfile.parent
    includes: list[IncludeDir] = []
    for raw in libfile.read_text(encoding="utf-8").splitlines():
        line = raw.split("--", 1)[0].strip()
        if line.startswith("include:"):
            parts = line[len("include:") :].split()
            includes.extend(str((base / part).resolve()) for part in parts)
    return includes or [str(base)]


@functools.cache
def _include_paths() -> tuple[IncludeDir, ...]:
    """Include dirs the reader needs to decode interfaces: project `src` + libraries.

    Must match what wrote the interface, or `decode` fails (it resolves
    module<->source via the include dirs).  Project `src` is `SRC` (the
    `aletheia.agda-lib` `include: src`); library dirs come from `~/.agda/libraries`.
    """
    paths: list[IncludeDir] = [str(SRC)]
    libraries = Path.home() / ".agda" / "libraries"
    if libraries.is_file():
        for raw in libraries.read_text(encoding="utf-8").splitlines():
            entry = raw.split("--", 1)[0].strip()
            libfile = Path(entry).expanduser()
            if entry and libfile.is_file():
                paths.extend(_lib_includes(libfile))
    return tuple(paths)


def candidate_queries(text: str) -> QueryMap:
    """Map each prunable import name to the imports that resolve it (per file).

    Mirrors the gate's candidate set (:func:`tools._agda_opens.open_check_names`)
    but keeps the module + original-name association the reader needs.  A
    ``using (n)`` entry yields ``ImportRef(module, n)`` (a ``module `` prefix
    stripped); a ``renaming (src to dst)`` candidate ``dst`` yields
    ``ImportRef(module, src)`` — the elaborated term references the origin.
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
            qmap.setdefault(name, []).append(ImportRef(open_info.module, name))
        for src, dst in open_info.renaming:
            qmap.setdefault(dst, []).append(ImportRef(open_info.module, src))
    return qmap


def _present_agdai(rels: set[RelPath]) -> AgdaiFiles:
    """Resolve each rel's `.agdai` (keeping only those that exist), both directions."""
    by_rel = {rel: _agdai_path(rel) for rel in rels if _agdai_path(rel).is_file()}
    return AgdaiFiles(by_rel, {str(p): rel for rel, p in by_rel.items()})


def invoke_reader(
    query_lines: list[QueryLine], include_paths: tuple[IncludeDir, ...]
) -> list[OutputLine]:
    """Run the reader binary over the query lines (with `include_paths`); stdout lines.

    Shared by this module's driver (project + stdlib include paths) and the fixture
    test (a scratch dir), so the build + subprocess call lives in one place.
    """
    binary = build_reader()
    env = {**os.environ, "AGDA_IWYU_INCLUDE_PATHS": ":".join(include_paths)}
    result = subprocess.run(
        [str(binary)],
        input="\n".join(query_lines) + "\n",
        capture_output=True,
        text=True,
        env=env,
        check=False,
    )
    return result.stdout.splitlines()


def _decode_verdict(line: str, rel_by_path: dict[AgdaiPath, RelPath]) -> DecodedVerdict | None:
    """Decode one reader JSONL line into its name query + verdict, or None to skip."""
    f = verdict_fields(line)
    if f is None:
        return None
    rel = rel_by_path.get(f.path)
    if rel is None:
        return None
    return DecodedVerdict(NameQuery(rel, f.module, f.name), f.verdict)


def run_reader(queries: list[NameQuery]) -> Verdicts:
    """Run the reader over name queries; map each to its verdict.

    Only queries whose file has a present `.agdai` are sent (the caller treats a
    missing verdict as "reader could not judge" → defer to the oracle).
    """
    if not queries:
        return {}
    agdai = _present_agdai({q.rel for q in queries})
    lines = [
        f"{agdai.by_rel[q.rel]}\t{q.module}\t{q.name}" for q in queries if q.rel in agdai.by_rel
    ]
    if not lines:
        return {}
    verdicts: Verdicts = {}
    for line in invoke_reader(lines, _include_paths()):
        decoded = _decode_verdict(line, agdai.rel_by_path)
        if decoded is not None:
            verdicts[decoded.query] = decoded.verdict
    return verdicts


def _decode_wildcard(line: str, rel_by_path: dict[AgdaiPath, RelPath]) -> DecodedWild | None:
    """Decode one wildcard reader JSONL line into its query + used subset, or None."""
    f = wildcard_fields(line)
    if f is None:
        return None
    rel = rel_by_path.get(f.path)
    if rel is None:
        return None
    return DecodedWild(WildQuery(rel, f.module), f.used)


def read_wildcards(queries: list[WildQuery]) -> WildUsed:
    """Run wildcard queries; map each to the USED subset of its module's exports."""
    if not queries:
        return {}
    agdai = _present_agdai({q.rel for q in queries})
    lines = [f"{agdai.by_rel[q.rel]}\t{q.module}\t*" for q in queries if q.rel in agdai.by_rel]
    if not lines:
        return {}
    out: WildUsed = {}
    for line in invoke_reader(lines, _include_paths()):
        parsed = _decode_wildcard(line, agdai.rel_by_path)
        if parsed is not None:
            out[parsed.query] = parsed.used
    return out


def _reader_verdict(rel: RelPath, name: Name, qmap: QueryMap, verdicts: Verdicts) -> Verdict:
    """Aggregate a candidate's reader verdict across the imports that resolve it.

    USED if any query is USED; DEAD only if all are DEAD; otherwise UNRESOLVED
    (a missing or UNRESOLVED query → defer to the oracle, never DEAD).
    """
    results = [verdicts.get(NameQuery(rel, ref.module, ref.name)) for ref in qmap.get(name, [])]
    if not results or any(r is None for r in results):
        return "UNRESOLVED"
    if "USED" in results:
        return "USED"
    if all(r == "DEAD" for r in results):
        return "DEAD"
    return "UNRESOLVED"


class Differential(NamedTuple):
    """Per-file reader-vs-oracle tally: blocking FNs, safe over-keeps, agreements."""

    false_negs: int
    over_keeps: int
    agree: int


def _classify_file(
    rel: RelPath,
    cands: list[Name],
    qmap: QueryMap,
    verdicts: Verdicts,
    dead_set: set[Name],
) -> Differential:
    """Compare reader vs oracle per candidate.

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
    return Differential(false_negs, over_keeps, agree)


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
        NameQuery(rel, ref.module, ref.name)
        for rel, cands in swept.candidates.items()
        for name in cands
        for ref in qmaps[rel].get(name, [])
    ]
    verdicts = run_reader(queries)
    total = Differential(0, 0, 0)
    for rel, cands in swept.candidates.items():
        oracle_dead, _alive = process_names(agda, rel, cands, keep=False)
        d = _classify_file(rel, cands, qmaps[rel], verdicts, set(oracle_dead))
        total = Differential(
            total.false_negs + d.false_negs,
            total.over_keeps + d.over_keeps,
            total.agree + d.agree,
        )
    emit(
        f"=== reader-vs-oracle: {total.false_negs} FALSE NEGATIVE(s), "
        + f"{total.over_keeps} over-keep, {total.agree} agree ==="
    )
    return 1 if total.false_negs else 0


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
