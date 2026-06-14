# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
"""The single IWYU import tool for Agda — gate, narrower, and self-test.

One tool for the whole import story, all driven by the scope-aware `.agdai`
reader (engine: :mod:`tools._iwyu`).  In ONE warm `agda` process it judges
both kinds of import on the scoped files:

  * named imports (`using (n)` / `renaming (src to dst)`) → USED / DEAD /
    UNRESOLVED; a DEAD candidate is an unused import, UNRESOLVED is surfaced
    (never collapsed to DEAD);
  * wildcard `open import M` → DEAD / REDUNDANT / NARROWABLE.

Modes (mutually exclusive; default is a report):

  * `--check`  — gate: scope the files, refresh their `.agdai`, run both
    analyses, exit 1 if anything is DEAD / REDUNDANT / NARROWABLE / UNRESOLVED
    or any wildcard `.agdai` was unreadable.
  * `--apply`  — rewrite each wildcard finding in place (NARROWABLE → `using
    (...)`, DEAD / REDUNDANT → delete), verifying each rewrite type-checks and
    restoring it otherwise.  Dead NAMED imports are reported, not auto-removed
    (removing one name from a `using (...)` is trivial manual work).
  * `--self-test` — validate the reader itself against the synthetic fixture
    matrix (`tools/agda-iwyu-reader/test/`); this is the reader's correctness
    gate (it replaced the retired recompile oracle), so CI runs it always.

Scope: `--all` (whole tree), `--diff` (changed vs `main`), or explicit paths.

Invoke: `python -m tools.iwyu (--check | --apply | --self-test) [--all | --diff | FILE.agda ...]`.
"""

from __future__ import annotations

import shutil
import sys
import tempfile
from pathlib import Path
from typing import NamedTuple

from tools._agda_opens import find_opens
from tools._common import (
    emit,
    install_restore_handlers,
    run_capture,
    track_inflight,
    untrack_inflight,
)
from tools._iwyu import (
    DEAD,
    NARROWABLE,
    PKG,
    REDUNDANT,
    Analysis,
    Finding,
    GateResult,
    ModulePath,
    analyze_dead_imports,
    analyze_wildcards,
    candidate_queries,
    classify_wildcard,
    explicit_from,
    invoke_reader,
    rewrite,
    verdict_fields,
    wildcard_fields,
)
from tools._resources import cpu_budget
from tools._warm import AGDA_BIN, SRC, RelPath, WarmAgda, run_warm_gate

FIXTURES = PKG / "test" / "fixtures"
MANIFEST = PKG / "test" / "manifest.tsv"
WILDCARD_MANIFEST = PKG / "test" / "wildcard_manifest.tsv"


# ─── Reporting ─────────────────────────────────────────────────────────────────


def _report(dead: GateResult, wild: Analysis) -> int:
    """Print every finding across both analyses; return the actionable+unresolved count.

    DEAD named imports, then wildcard findings (NARROWABLE / DEAD / REDUNDANT),
    then the surfaced ones the reader could not judge (a missing `.agdai`).
    """
    actionable = 0
    for d in dead.dead:
        emit(f"  DEAD {d.rel}: {d.name} (unused named import — remove)")
        actionable += 1
    for f in wild.findings:
        if f.kind == NARROWABLE:
            using = "; ".join(sorted(f.needed))
            emit(f"  NARROWABLE {f.rel}: open import {f.module} → using ({using})")
        else:  # DEAD / REDUNDANT wildcard
            emit(f"  {f.kind} {f.rel}: open import {f.module} (remove)")
        actionable += 1
    unresolved = len(dead.unresolved) + len(wild.skipped)
    for u in dead.unresolved:  # surfaced, never silently dropped, never flagged DEAD
        emit(f"  ⚠️ UNRESOLVED {u.rel}: {u.name} (reader could not read its .agdai)")
    for q in wild.skipped:
        emit(f"  ⚠️ SKIPPED {q.rel}: open import {q.module} (reader could not read its .agdai)")
    emit(
        f"=== iwyu: {actionable} finding(s), {unresolved} unresolved, across "
        + f"{len(dead.dead)} dead-named + {len(wild.findings)} wildcard ==="
    )
    return actionable + unresolved


# ─── --apply (wildcard rewrites) ───────────────────────────────────────────────


def _apply(agda: WarmAgda, findings: list[Finding]) -> int:
    """Rewrite each file's wildcard findings, verifying each rewrite type-checks.

    A rewritten file is reloaded; if it fails (a use the reader did not capture),
    the original is restored and the file skipped.  Crash-safe: a rewritten file
    is restored on interrupt.  Returns the number of files successfully rewritten.
    """
    by_file: dict[RelPath, dict[ModulePath, Finding]] = {}
    for f in findings:
        if f.kind in (DEAD, REDUNDANT, NARROWABLE):
            by_file.setdefault(f.rel, {})[f.module] = f
    install_restore_handlers()
    applied = 0
    for rel, fmap in by_file.items():
        path = SRC / rel
        original = path.read_text(encoding="utf-8")
        new = rewrite(original, fmap)
        if new == original:
            continue
        kept = False
        try:
            track_inflight(str(path), original)
            _ = path.write_text(new, encoding="utf-8")
            if agda.load(str(path)).ok:
                kept = True
                applied += 1
                emit(f"  applied {rel} ({len(fmap)} wildcard finding(s))")
            else:
                emit(f"  SKIP {rel}: rewrite did not type-check — restored")
        finally:
            if not kept:
                _ = path.write_text(original, encoding="utf-8")
            untrack_inflight(str(path))
    return applied


# ─── --self-test (synthetic fixture matrix) ────────────────────────────────────


class Row(NamedTuple):
    """One name-query manifest expectation: fixture module, queried import, verdict."""

    consumer: str
    module: str
    name: str
    expected: str


class WildRow(NamedTuple):
    """One wildcard manifest expectation: a module's USED subset and its finding."""

    consumer: str
    module: str
    used: frozenset[str]
    finding: str


def _read_manifest() -> list[Row]:
    """Parse `manifest.tsv` (a header line then ``consumer⇥module⇥name⇥verdict``)."""
    rows: list[Row] = []
    for i, line in enumerate(MANIFEST.read_text(encoding="utf-8").splitlines()):
        if i == 0 or not line.strip():
            continue
        consumer, module, name, expected = line.split("\t")
        rows.append(Row(consumer, module, name, expected))
    return rows


def _read_wildcard_manifest() -> list[WildRow]:
    """Parse `wildcard_manifest.tsv` (header then ``consumer⇥module⇥used,csv⇥finding``)."""
    rows: list[WildRow] = []
    for i, line in enumerate(WILDCARD_MANIFEST.read_text(encoding="utf-8").splitlines()):
        if i == 0 or not line.strip():
            continue
        consumer, module, used, finding = line.split("\t")
        rows.append(WildRow(consumer, module, frozenset(n for n in used.split(",") if n), finding))
    return rows


def _typecheck_fixtures(scratch: Path) -> None:
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
            [
                str(AGDA_BIN),
                "+RTS",
                f"-N{cpu_budget()}",
                "-M4G",
                "-RTS",
                "--safe",
                "--without-K",
                agda.name,
            ],
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


class AliasKey(NamedTuple):
    """Identifies one fixture renaming candidate: fixture stem, source module, origin name.

    The same (consumer, module, name) triple a manifest `Row` carries, so the
    self-test can look up the alias position a `Row` needs.
    """

    consumer: str
    module: ModulePath
    name: str


def _fixture_alias_positions() -> dict[AliasKey, int]:
    """Map each fixture's renaming candidate to its alias source position.

    Keyed the same way a manifest `Row` is identified, so the self-test sends the
    reader the SAME alias position the production driver
    (:func:`candidate_queries`) computes.  Non-renamed entries map to 0.
    """
    out: dict[AliasKey, int] = {}
    for agda in FIXTURES.glob("*.agda"):
        for refs in candidate_queries(agda.read_text(encoding="utf-8")).values():
            for ref in refs:
                out[AliasKey(agda.stem, ref.module, ref.name)] = ref.alias_pos
    return out


def _self_test() -> int:
    """Type-check the fixtures, run the reader, assert the verdict + wildcard manifests.

    Covers both name queries (USED/DEAD/UNRESOLVED) and wildcard queries (the used
    subset of a wildcard-opened module).  This is the reader's correctness gate
    (it replaced the retired recompile oracle).  Exit 1 on any mismatch.
    """
    rows = _read_manifest()
    wrows = _read_wildcard_manifest()
    alias = _fixture_alias_positions()
    with tempfile.TemporaryDirectory() as tmp:
        scratch = Path(tmp)
        _typecheck_fixtures(scratch)
        queries = [
            "\t".join(
                [
                    str(scratch / (r.consumer + ".agdai")),
                    r.module,
                    r.name,
                    str(alias.get(AliasKey(r.consumer, r.module, r.name), 0)),
                ]
            )
            for r in rows
        ]
        queries += [f"{scratch / (w.consumer + '.agdai')}\t{w.module}\t*" for w in wrows]
        out = invoke_reader(queries, (str(scratch),))
    fails = _check_verdicts(rows, out) + _check_wildcards(wrows, out)
    total = len(rows) + len(wrows)
    emit(f"=== iwyu self-test: {total - fails}/{total} fixtures pass ===")
    return 1 if fails else 0


# ─── CLI ───────────────────────────────────────────────────────────────────────


def main() -> int:
    """Dispatch on the mode flag (`--check` / `--apply` / `--self-test`).

    `--self-test` ignores the scope (it runs the synthetic fixtures).  `--check`
    and `--apply` resolve the scope (`--all` / `--diff` / explicit paths), refresh
    each file's `.agdai` in one warm process, then run both analyses.  `--check`
    exits 1 on any finding or unresolved candidate; `--apply` rewrites wildcard
    findings and exits 0; the default is a non-failing report.
    """
    argv = sys.argv[1:]
    if "--self-test" in argv:
        return _self_test()
    check = "--check" in argv
    apply = "--apply" in argv

    def action(agda: WarmAgda, files: list[RelPath]) -> int:
        dead = analyze_dead_imports(files)
        wild = analyze_wildcards(files)
        findings = _report(dead, wild)
        if apply:
            emit(f"=== applied {_apply(agda, wild.findings)} file(s) ===")
            return 0
        return 1 if (check and findings) else 0

    return run_warm_gate(argv, action)


if __name__ == "__main__":
    sys.exit(main())
