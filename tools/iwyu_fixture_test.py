#!/usr/bin/env python3
# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
"""Synthetic-fixture test for the `agda-iwyu-reader` verdict logic.

The impure half of the validation split: the reader's used-set + scope
resolution is checked against self-contained Agda fixtures whose verdicts are
known BY CONSTRUCTION (`tools/agda-iwyu-reader/test/manifest.tsv`), never the
live tree (a contributor can rewrite any tree file).  Covers every use mechanism
— re-export value, Function-copy module, datatype/constructor copy, chained
re-export, private import, renaming, operator, instance/inferred use, pattern
synonym, record projection, aliased duplicate — AND the true-positive DEAD cases
(a `using`-listed name that is never used must be called DEAD).

Type-checks the fixtures in a scratch dir (agda runs FROM that dir: with no
`.agda-lib`, the project root is the cwd, so a leaf module `Origin` is reached as
`Origin.agda`), builds the reader, and asserts two manifests: `manifest.tsv`
(name queries → USED/DEAD/UNRESOLVED) and `wildcard_manifest.tsv` (a wildcard
`open import M` → the USED subset of M's exports, which narrowing/redundancy is
judged from — including inferred uses that body-token tools miss).  Exit 1 on any
mismatch.

Invoke: `python -m tools.iwyu_fixture_test`.
"""

from __future__ import annotations

import json
import os
import shutil
import subprocess
import sys
import tempfile
from pathlib import Path
from typing import NamedTuple, cast

from tools._common import emit, run_capture
from tools.iwyu_reader import build_reader
from tools.prune_unused_imports import AGDA_BIN

PKG = Path(__file__).resolve().parent / "agda-iwyu-reader"
FIXTURES = PKG / "test" / "fixtures"
MANIFEST = PKG / "test" / "manifest.tsv"
WILDCARD_MANIFEST = PKG / "test" / "wildcard_manifest.tsv"


class Row(NamedTuple):
    """One manifest expectation: fixture module, queried import, and verdict."""

    consumer: str
    module: str
    name: str
    expected: str


class WildRow(NamedTuple):
    """One wildcard expectation: the USED subset of a wildcard-opened module."""

    consumer: str
    module: str
    used: frozenset[str]


def read_manifest() -> list[Row]:
    """Parse `manifest.tsv` (a header line then ``consumer⇥module⇥name⇥verdict``)."""
    rows: list[Row] = []
    for i, line in enumerate(MANIFEST.read_text(encoding="utf-8").splitlines()):
        if i == 0 or not line.strip():
            continue
        consumer, module, name, expected = line.split("\t")
        rows.append(Row(consumer, module, name, expected))
    return rows


def read_wildcard_manifest() -> list[WildRow]:
    """Parse `wildcard_manifest.tsv` (header then ``consumer⇥module⇥used,comma,sep``)."""
    rows: list[WildRow] = []
    for i, line in enumerate(WILDCARD_MANIFEST.read_text(encoding="utf-8").splitlines()):
        if i == 0 or not line.strip():
            continue
        consumer, module, *rest = line.split("\t")
        used = rest[0] if rest else ""
        rows.append(WildRow(consumer, module, frozenset(n for n in used.split(",") if n)))
    return rows


def typecheck_fixtures(scratch: Path) -> None:
    """Copy every fixture into `scratch` and type-check it from there.

    Agda runs with `scratch` as cwd so its (no-`.agda-lib`) project root is the
    scratch dir; otherwise a leaf module fails `ModuleNameDoesntMatchFileName`.
    The fixtures are self-contained (no stdlib), so a bare `--safe --without-K`
    check suffices and also writes each `.agdai` the reader will read.
    """
    for agda in sorted(FIXTURES.glob("*.agda")):
        _ = shutil.copy(agda, scratch / agda.name)
    for agda in sorted(scratch.glob("*.agda")):
        result = run_capture(
            [str(AGDA_BIN), "+RTS", "-N4", "-M4G", "-RTS", "--safe", "--without-K", agda.name],
            cwd=scratch,
        )
        if result.returncode != 0:
            emit(result.stdout)
            emit(result.stderr)
            message = f"fixture failed to type-check: {agda.name}"
            raise RuntimeError(message)


def _parse_verdict(line: str) -> tuple[tuple[str, str, str], str] | None:
    """Decode one reader JSONL line into ((consumer-stem, mod, name), verdict)."""
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
    return (Path(cast("str", path)).stem, cast("str", mod), cast("str", name)), cast("str", verdict)


def _parse_wildcard(line: str) -> tuple[tuple[str, str], frozenset[str]] | None:
    """Decode one wildcard reader JSONL line into ((consumer-stem, mod), used-set)."""
    line = line.strip()
    if not line.startswith("{"):
        return None
    raw = cast("object", json.loads(line))
    if not isinstance(raw, dict):
        return None
    obj = cast("dict[str, object]", raw)
    path, mod, name, used = obj.get("path"), obj.get("mod"), obj.get("name"), obj.get("used")
    if not (
        isinstance(path, str) and isinstance(mod, str) and name == "*" and isinstance(used, list)
    ):
        return None
    names = frozenset(u for u in cast("list[object]", used) if isinstance(u, str))
    return (Path(path).stem, mod), names


def run_reader(scratch: Path, query_lines: list[str]) -> list[str]:
    """Run the reader over the given query lines; return its stdout lines."""
    binary = build_reader()
    env = {**os.environ, "AGDA_IWYU_INCLUDE_PATHS": str(scratch)}
    result = subprocess.run(
        [str(binary)],
        input="\n".join(query_lines) + "\n",
        capture_output=True,
        text=True,
        env=env,
        check=False,
    )
    return result.stdout.splitlines()


def _check_verdicts(rows: list[Row], out: list[str]) -> int:
    """Assert each name query's verdict matches the manifest; return the fail count."""
    verdicts = dict(p for line in out if (p := _parse_verdict(line)) is not None)
    fails = 0
    for r in rows:
        actual = verdicts.get((r.consumer, r.module, r.name), "<none>")
        if actual != r.expected:
            emit(f"  FAIL {r.consumer} {r.module}={r.name}: expected {r.expected}, got {actual}")
            fails += 1
    return fails


def _check_wildcards(wrows: list[WildRow], out: list[str]) -> int:
    """Assert each wildcard query's used subset matches the manifest; return fails."""
    wilds = dict(p for line in out if (p := _parse_wildcard(line)) is not None)
    fails = 0
    for w in wrows:
        actual = wilds.get((w.consumer, w.module))
        if actual != w.used:
            emit(f"  FAIL {w.consumer} {w.module}=*: expected {sorted(w.used)}, got {actual}")
            fails += 1
    return fails


def main() -> int:
    """Type-check the fixtures, run the reader, assert the verdict + wildcard manifests.

    Covers both name queries (USED/DEAD/UNRESOLVED) and wildcard queries (the used
    subset of a wildcard-opened module).  Exit 1 on any mismatch.
    """
    rows = read_manifest()
    wrows = read_wildcard_manifest()
    with tempfile.TemporaryDirectory() as tmp:
        scratch = Path(tmp)
        typecheck_fixtures(scratch)
        queries = [f"{scratch / (r.consumer + '.agdai')}\t{r.module}\t{r.name}" for r in rows]
        queries += [f"{scratch / (w.consumer + '.agdai')}\t{w.module}\t*" for w in wrows]
        out = run_reader(scratch, queries)
    fails = _check_verdicts(rows, out) + _check_wildcards(wrows, out)
    total = len(rows) + len(wrows)
    emit(f"=== iwyu-reader fixtures: {total - fails}/{total} pass ===")
    return 1 if fails else 0


if __name__ == "__main__":
    sys.exit(main())
