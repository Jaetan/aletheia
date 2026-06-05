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
`Origin.agda`), builds the reader, runs it over the manifest queries, and asserts
each verdict.  Exit 1 on any mismatch.

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


class Row(NamedTuple):
    """One manifest expectation: fixture module, queried import, and verdict."""

    consumer: str
    module: str
    name: str
    expected: str


def read_manifest() -> list[Row]:
    """Parse `manifest.tsv` (a header line then ``consumer⇥module⇥name⇥verdict``)."""
    rows: list[Row] = []
    for i, line in enumerate(MANIFEST.read_text(encoding="utf-8").splitlines()):
        if i == 0 or not line.strip():
            continue
        consumer, module, name, expected = line.split("\t")
        rows.append(Row(consumer, module, name, expected))
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


def run_reader(scratch: Path, rows: list[Row]) -> dict[tuple[str, str, str], str]:
    """Run the reader over the manifest queries; map (consumer, mod, name) → verdict."""
    binary = build_reader()
    lines = [f"{scratch / (r.consumer + '.agdai')}\t{r.module}\t{r.name}" for r in rows]
    env = {**os.environ, "AGDA_IWYU_INCLUDE_PATHS": str(scratch)}
    result = subprocess.run(
        [str(binary)],
        input="\n".join(lines) + "\n",
        capture_output=True,
        text=True,
        env=env,
        check=False,
    )
    verdicts: dict[tuple[str, str, str], str] = {}
    for line in result.stdout.splitlines():
        parsed = _parse_verdict(line)
        if parsed is not None:
            verdicts[parsed[0]] = parsed[1]
    return verdicts


def main() -> int:
    """Type-check the fixtures, run the reader, assert every manifest verdict.

    Exit 1 on any mismatch (including an UNRESOLVED where a precise verdict is
    expected); exit 0 when all match.
    """
    rows = read_manifest()
    with tempfile.TemporaryDirectory() as tmp:
        scratch = Path(tmp)
        typecheck_fixtures(scratch)
        verdicts = run_reader(scratch, rows)
    fails = 0
    for r in rows:
        actual = verdicts.get((r.consumer, r.module, r.name), "<none>")
        if actual != r.expected:
            emit(f"  FAIL {r.consumer} {r.module}={r.name}: expected {r.expected}, got {actual}")
            fails += 1
    emit(f"=== iwyu-reader fixtures: {len(rows) - fails}/{len(rows)} pass ===")
    return 1 if fails else 0


if __name__ == "__main__":
    sys.exit(main())
