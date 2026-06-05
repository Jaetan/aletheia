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

import shutil
import sys
import tempfile
from pathlib import Path
from typing import NamedTuple

from tools._agda_opens import find_opens
from tools._common import emit, run_capture
from tools._warm import AGDA_BIN
from tools.iwyu_narrow import classify_wildcard, explicit_from
from tools.iwyu_reader import invoke_reader, verdict_fields, wildcard_fields

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
    """One wildcard expectation: a module's USED subset and its narrowing finding."""

    consumer: str
    module: str
    used: frozenset[str]
    finding: str


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
    """Parse `wildcard_manifest.tsv` (header then ``consumer⇥module⇥used,csv⇥finding``)."""
    rows: list[WildRow] = []
    for i, line in enumerate(WILDCARD_MANIFEST.read_text(encoding="utf-8").splitlines()):
        if i == 0 or not line.strip():
            continue
        consumer, module, used, finding = line.split("\t")
        rows.append(WildRow(consumer, module, frozenset(n for n in used.split(",") if n), finding))
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


def _check_verdicts(rows: list[Row], out: list[str]) -> int:
    """Assert each name query's verdict matches the manifest; return the fail count."""
    verdicts = {
        (Path(f.path).stem, f.module, f.name): f.verdict
        for line in out
        if (f := verdict_fields(line)) is not None
    }
    fails = 0
    for r in rows:
        actual = verdicts.get((r.consumer, r.module, r.name), "<none>")
        if actual != r.expected:
            emit(f"  FAIL {r.consumer} {r.module}={r.name}: expected {r.expected}, got {actual}")
            fails += 1
    return fails


def _check_wildcards(wrows: list[WildRow], out: list[str]) -> int:
    """Assert each wildcard's used subset (reader) AND its narrowing finding (pure logic).

    The used subset is the reader's; the finding is `classify_wildcard` over that
    subset and the names the fixture imports explicitly from the module — so both
    the impure extraction and the pure classification are validated synthetically.
    """
    wilds = {
        (Path(f.path).stem, f.module): f.used
        for line in out
        if (f := wildcard_fields(line)) is not None
    }
    fails = 0
    for w in wrows:
        used = wilds.get((w.consumer, w.module))
        if used is None or used != w.used:
            emit(f"  FAIL {w.consumer} {w.module}=*: expected used {sorted(w.used)}, got {used}")
            fails += 1
            continue
        opens = find_opens((FIXTURES / f"{w.consumer}.agda").read_text(encoding="utf-8"))
        finding = classify_wildcard(used, explicit_from(opens, w.module)).kind
        if finding != w.finding:
            emit(f"  FAIL {w.consumer} {w.module}=*: expected finding {w.finding}, got {finding}")
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
        out = invoke_reader(queries, (str(scratch),))
    fails = _check_verdicts(rows, out) + _check_wildcards(wrows, out)
    total = len(rows) + len(wrows)
    emit(f"=== iwyu-reader fixtures: {total - fails}/{total} pass ===")
    return 1 if fails else 0


if __name__ == "__main__":
    sys.exit(main())
