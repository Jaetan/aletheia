#!/usr/bin/env python3
# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
"""Warm-process dead-import CLEANUP — removes confirmed-dead imports in place.

Sibling of :mod:`tools.warm_dead_imports` (the detection gate): over the shared
CLI shell (``run_warm_tool``) it runs the same grammar-complete sieve, then for
each candidate REMOVES it and warm-recompiles, KEEPING the removal iff the file
still type-checks within its baseline warning count (confirm-then-keep).  An
inferred-use false positive never type-checks clean, so it is left untouched —
only genuinely-dead imports are removed.

Unlike :mod:`tools.warm_prune` (the flat oracle, built on ``parse_imports``,
which silently drops multi-line ``using`` clauses), this uses the same
``_agda_opens`` scan as the gate, so it removes exactly the dead imports the
gate detects.  Crash-safe: each in-flight write is registered, and a kept
removal has already type-checked, so an interrupt leaves a consistent file.

Invoke: ``python -m tools.warm_apply (--all | --diff | FILE.agda ...)``
"""

from __future__ import annotations

import sys

from tools.warm_dead_imports import (
    Candidates,
    SweepResult,
    WarmAgda,
    drive_dead,
    run_warm_tool,
)


def apply_all(agda: WarmAgda, candidates: Candidates) -> int:
    """Remove every confirmed-dead candidate in place (confirm-then-keep).

    The shared per-file driver :func:`tools.warm_dead_imports.drive_dead` with
    ``keep=True``: a name whose removal still type-checks within the file's
    baseline warning count is dropped for good; an inferred-use false positive
    (never type-checks clean) is left untouched.  Returns the removed count.
    """
    return drive_dead(
        agda, candidates, keep=True, verb="apply", fmt=lambda dead, _alive: f"REMOVED={dead or '—'}"
    )


def main() -> int:
    """Remove confirmed-dead imports in place across the scoped files (always exit 0).

    Scope flags mirror the gate: ``--all`` (whole tree) / ``--diff`` (changed vs
    main) / explicit paths — resolved by the shared ``run_warm_tool`` shell.
    """

    def action(agda: WarmAgda, swept: SweepResult) -> int:
        if swept.candidates:
            _ = apply_all(agda, swept.candidates)
        return 0  # cleanup, not a gate

    return run_warm_tool(sys.argv[1:], action)


if __name__ == "__main__":
    sys.exit(main())
