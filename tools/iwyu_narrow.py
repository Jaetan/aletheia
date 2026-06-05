#!/usr/bin/env python3
# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
"""IWYU narrowing / redundancy driver for wildcard `open import M` (Route A).

For each WILDCARD `open import M` (an `open import` with no `using`/`hiding`/
`renaming`/`public`), the scope-aware `.agdai` reader reports the USED subset of
M's exports (:func:`tools.iwyu_reader.read_wildcards`), capturing the
inferred/implicit uses that body-token tools miss.  From that subset and the
names the file ALSO imports explicitly from M, each wildcard is classified:

  * DEAD       — nothing from M is used        → remove the wildcard.
  * REDUNDANT  — every used name is also imported explicitly → remove the wildcard
                 (the explicit imports already cover it; "explicit > wildcard").
  * NARROWABLE — M supplies used names not otherwise imported → replace the
                 wildcard with `open import M using (those names)`.

This is the IMPURE-input / PURE-logic split: the used subset is the reader's
(validated by the synthetic fixture matrix, :mod:`tools.iwyu_fixture_test`); the
classification :func:`classify_wildcard` is pure (validated there too).  The
driver refreshes each scoped file's `.agdai` via one warm process first, so the
reader sees current interfaces.

Duplicate-explicit redundancy (the same name imported twice) is NOT handled here:
the interface scope dedups providers, so it is not soundly detectable from the
reader (it needs recompile-confirm).

Invoke: `python -m tools.iwyu_narrow [--check|--apply] (--all | --diff | FILE.agda ...)`.
`--check` exits 1 if any finding is reported OR any wildcard was skipped (an
unreadable `.agdai` — surfaced, never silently passed); `--apply` rewrites each
finding in place, verifying it type-checks and restoring it otherwise.
"""

from __future__ import annotations

import sys
from typing import TYPE_CHECKING, NamedTuple

from tools._agda_opens import ModulePath, find_opens
from tools._common import (
    emit,
    install_restore_handlers,
    track_inflight,
    untrack_inflight,
)
from tools._warm import SRC, Name, RelPath, WarmAgda, run_warm_gate
from tools.iwyu_reader import WildQuery, read_wildcards

if TYPE_CHECKING:
    from tools._agda_opens import OpenInfo

# How a wildcard `open import M` is classified.
type WildcardKind = str  # one of the three constants below
DEAD = "DEAD"
REDUNDANT = "REDUNDANT"
NARROWABLE = "NARROWABLE"


class Classification(NamedTuple):
    """A wildcard's verdict and, for NARROWABLE, the `using` set to narrow to."""

    kind: WildcardKind
    needed: frozenset[Name]  # the names to narrow to (empty for DEAD / REDUNDANT)


class Finding(NamedTuple):
    """One classified wildcard open, located by file + module."""

    rel: RelPath
    module: ModulePath
    kind: WildcardKind
    needed: frozenset[Name]


class LineEdit(NamedTuple):
    """A pending source edit: the 0-based line of a wildcard open + its finding."""

    line: int
    finding: Finding


def is_wildcard(open_info: OpenInfo) -> bool:
    """Return True iff `open_info` is a bare wildcard ``open import M`` (a narrowing target).

    Excludes `using`/`renaming`/`hiding`/`public` opens and bare `import M`
    (qualified-only): only an unrestricted unqualified open brings M's whole
    export set and is a narrowing candidate.
    """
    return (
        open_info.is_open
        and open_info.is_import
        and not open_info.has_using
        and not open_info.renaming
        and not open_info.hiding_names
        and not open_info.has_public
    )


def explicit_from(opens: list[OpenInfo], module: ModulePath) -> frozenset[Name]:
    """Names explicitly imported from `module` by NON-wildcard, non-public opens.

    The `using (...)` entries (a ``module `` prefix stripped) plus `renaming`
    destinations of every other open of the same module — the set a wildcard's
    used names must be covered by for the wildcard to be REDUNDANT.
    """
    names: set[Name] = set()
    for o in opens:
        if o.module != module or o.has_public or is_wildcard(o):
            continue
        if o.is_open and (o.has_using or o.renaming):
            names |= {
                n[len("module ") :].strip() if n.startswith("module ") else n for n in o.using_names
            }
            names |= {dst for _src, dst in o.renaming}
    return frozenset(names)


def classify_wildcard(used: frozenset[Name], explicit: frozenset[Name]) -> Classification:
    """Classify a wildcard from its used subset and the file's explicit imports.

    Pure (validated synthetically): empty used → DEAD; every used name also
    explicit → REDUNDANT; otherwise NARROWABLE to the used names not already
    imported explicitly (narrowing to just those avoids creating a duplicate).
    """
    needed = used - explicit
    if not used:
        return Classification(DEAD, frozenset())
    if not needed:
        return Classification(REDUNDANT, frozenset())
    return Classification(NARROWABLE, needed)


class Analysis(NamedTuple):
    """The result of classifying a scope's wildcards: findings + the unreadable ones.

    `skipped` are wildcard opens whose `.agdai` the reader could not read — surfaced
    (not silently dropped), so the gate fails loud rather than under-reporting.
    """

    findings: list[Finding]
    skipped: list[WildQuery]


def analyze(rels: list[RelPath]) -> Analysis:
    """Classify every wildcard open across the scoped files (`.agdai` must be fresh)."""
    opens_by_rel = {rel: find_opens((SRC / rel).read_text(encoding="utf-8")) for rel in rels}
    queries = sorted(
        {
            WildQuery(rel, o.module)
            for rel, opens in opens_by_rel.items()
            for o in opens
            if is_wildcard(o)
        }
    )
    used_by = read_wildcards(queries)
    findings = [
        Finding(
            q.rel,
            q.module,
            *classify_wildcard(used_by[q], explicit_from(opens_by_rel[q.rel], q.module)),
        )
        for q in queries
        if q in used_by
    ]
    skipped = [q for q in queries if q not in used_by]
    return Analysis(findings, skipped)


def rewrite(text: str, findings: dict[ModulePath, Finding]) -> str:
    """Apply each module's finding to its wildcard open(s) in `text`.

    NARROWABLE → `open import M using (needed)`; DEAD / REDUNDANT → delete the
    line.  Edits are applied bottom-up so earlier line numbers stay valid, and
    the original indentation is preserved.  Targets only line-leading wildcard
    `open import M` directives (what `is_wildcard` matches).
    """
    lines = text.splitlines(keepends=True)
    edits = [
        LineEdit(text[: o.span[0]].count("\n"), findings[o.module])
        for o in find_opens(text)
        if is_wildcard(o) and o.module in findings
    ]
    for e in sorted(edits, key=lambda x: x.line, reverse=True):
        line = lines[e.line]
        indent = line[: len(line) - len(line.lstrip())]
        if e.finding.kind == NARROWABLE:
            using = "; ".join(sorted(e.finding.needed))
            lines[e.line] = f"{indent}open import {e.finding.module} using ({using})\n"
        else:  # DEAD / REDUNDANT — the wildcard provides nothing uniquely used
            del lines[e.line]
    return "".join(lines)


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


def _report(result: Analysis) -> int:
    """Print each actionable finding + any skipped wildcards; return findings count."""
    actionable = 0
    for f in result.findings:
        if f.kind == NARROWABLE:
            using = "; ".join(sorted(f.needed))
            emit(f"  NARROWABLE {f.rel}: open import {f.module} → using ({using})")
            actionable += 1
        elif f.kind in (DEAD, REDUNDANT):
            emit(f"  {f.kind} {f.rel}: open import {f.module} (remove)")
            actionable += 1
    for q in result.skipped:  # surfaced, never silently dropped
        emit(f"  ⚠️ SKIPPED {q.rel}: open import {q.module} (reader could not read its .agdai)")
    total = len(result.findings) + len(result.skipped)
    emit(
        f"=== iwyu wildcards: {actionable} finding(s), {len(result.skipped)} skipped, "
        + f"across {total} wildcard open(s) ==="
    )
    return actionable


def main() -> int:
    """Scope files, refresh their `.agdai`, classify every wildcard open, report.

    Scope mirrors the dead-import gate (`--all` / `--diff` / explicit paths).
    `--apply` rewrites each finding (verifying it type-checks, restoring on
    failure); `--check` exits 1 if any finding is reported OR any wildcard was
    skipped (fail loud — never silently pass an unreadable `.agdai`).  `--check`
    is ignored under `--apply`.  Otherwise exit 0 after reporting.
    """
    check = "--check" in sys.argv[1:]
    apply = "--apply" in sys.argv[1:]

    def action(agda: WarmAgda, files: list[RelPath]) -> int:
        result = analyze(files)
        actionable = _report(result)
        if apply:
            emit(f"=== applied {_apply(agda, result.findings)} file(s) ===")
            return 0
        return 1 if (check and (actionable or result.skipped)) else 0

    return run_warm_gate(sys.argv[1:], action)


if __name__ == "__main__":
    sys.exit(main())
