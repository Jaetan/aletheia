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

Invoke: `python -m tools.iwyu_narrow [--check] (--all | --diff | FILE.agda ...)`.
With `--check` the exit code is 1 if any finding is reported (strict gate).
"""

from __future__ import annotations

import sys
from typing import TYPE_CHECKING, NamedTuple

from tools._agda_opens import ModulePath, find_opens
from tools._common import agda_tree_lock, emit
from tools.iwyu_reader import WildQuery, read_wildcards
from tools.warm_dead_imports import SRC, Name, RelPath, WarmAgda, select_files

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


def analyze(rels: list[RelPath]) -> list[Finding]:
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
    findings: list[Finding] = []
    for q in queries:
        if q not in used_by:
            continue  # reader could not read this `.agdai` — skip (no false claim)
        c = classify_wildcard(used_by[q], explicit_from(opens_by_rel[q.rel], q.module))
        findings.append(Finding(q.rel, q.module, c.kind, c.needed))
    return findings


def _report(findings: list[Finding]) -> int:
    """Print each actionable wildcard finding; return how many were reported."""
    actionable = 0
    for f in findings:
        if f.kind == NARROWABLE:
            using = "; ".join(sorted(f.needed))
            emit(f"  NARROWABLE {f.rel}: open import {f.module} → using ({using})")
            actionable += 1
        elif f.kind in (DEAD, REDUNDANT):
            emit(f"  {f.kind} {f.rel}: open import {f.module} (remove)")
            actionable += 1
    emit(f"=== iwyu wildcards: {actionable} finding(s) across {len(findings)} wildcard open(s) ===")
    return actionable


def main() -> int:
    """Scope files, refresh their `.agdai`, classify every wildcard open, report.

    Scope mirrors the dead-import gate (`--all` / `--diff` / explicit paths).
    With `--check`, exit 1 if any finding is reported; otherwise exit 0 (report).
    """
    args = [a for a in sys.argv[1:] if a != "--check"]
    check = "--check" in sys.argv[1:]
    files = select_files(args)
    if files is None:
        return 2
    if not files:
        return 0
    with agda_tree_lock(), WarmAgda() as agda:
        for rel in files:
            _ = agda.load(str(SRC / rel))  # refresh `.agdai` so the reader sees current interfaces
    findings = analyze(files)
    actionable = _report(findings)
    return 1 if (check and actionable) else 0


if __name__ == "__main__":
    sys.exit(main())
