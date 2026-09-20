# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
"""The shapes the mutation runner and its per-binding lanes share.

``MutationReport`` is one binding's result, serialized to ``<binding>.json``
under the run's artifact directory; the ``TypedDict`` classes are the shape of
``docs/MUTATION_BENCH.yaml`` and of the drift verdict written to
``summary.json``.  They live apart from the runner so the C++ lane
(``tools/mutation_cpp.py``) can build a report without importing the module
that drives it.
"""

from __future__ import annotations

from dataclasses import dataclass
from typing import NotRequired, TypedDict

# Last ``raw_log`` characters kept in the archived JSON (full log lands in the
# per-binding ``<binding>.raw.txt`` artifact alongside it).
RAW_LOG_TAIL_CHARS = 2000


class LedgerRow(TypedDict):
    """One recorded survivor: its mutator, file, source line and multiplicity."""

    mutator: str
    file: str
    text: str
    count: int


class Baseline(TypedDict):
    """The per-binding baseline block in ``docs/MUTATION_BENCH.yaml``."""

    survivors: NotRequired[int]
    timeout_ceiling: NotRequired[int]
    total_mutants: NotRequired[int]
    score_pct: NotRequired[int]
    run_at: NotRequired[str]
    survivors_ledger: NotRequired[list[LedgerRow]]


class BindingSpec(TypedDict):
    """One binding's entry under the YAML ``bindings`` mapping."""

    tool: NotRequired[str]
    baseline: NotRequired[Baseline]


class Spec(TypedDict):
    """The top-level shape of ``docs/MUTATION_BENCH.yaml``."""

    bindings: NotRequired[dict[str, BindingSpec]]


class DriftEntry(TypedDict):
    """One binding's drift verdict, serialized into ``summary.json``."""

    status: str
    error: NotRequired[str]
    observed_survivors: NotRequired[int]
    baseline_survivors: NotRequired[int]
    delta: NotRequired[int]
    observed_timeouts: NotRequired[int]
    timeout_ceiling: NotRequired[int]
    unrecorded_survivors: NotRequired[list[LedgerRow]]
    stale_ledger: NotRequired[list[LedgerRow]]


# A survivor's identity in the ledger: mutator, repository-relative file and
# the text of its source line.  Keyed on the text and not the line number, so
# an edit above the site does not move it, and an edit of the site does.
SurvivorKey = tuple[str, str, str]


@dataclass
class MutationReport:
    """Per-binding mutation result; serialized to ``<binding>.json``."""

    binding: str
    tool: str
    killed: int
    survived: int
    raw_log: str
    error: str | None = None
    # Mutants the tool started and could not finish, where it reports them.
    # They are neither killed nor survived, so a run that timed out on nearly
    # everything reports no survivors and full efficacy; the drift gate reads
    # this to refuse such a run.  ``None`` where the tool has no such bucket.
    timeouts: int | None = None

    @property
    def total_mutants(self) -> int:
        """Killed + survived (excludes not-covered / skipped per tool semantics)."""
        return self.killed + self.survived

    @property
    def score_pct(self) -> float:
        """Mutation score: killed / (killed + survived) * 100, or 0 if total is 0."""
        total = self.killed + self.survived
        return 100.0 * self.killed / total if total > 0 else 0.0

    def to_dict(self) -> dict[str, object]:
        """Materialize for JSON archival; truncates raw_log to last 2000 chars."""
        return {
            "binding": self.binding,
            "tool": self.tool,
            "total_mutants": self.total_mutants,
            "killed": self.killed,
            "survived": self.survived,
            "timeouts": self.timeouts,
            "score_pct": self.score_pct,
            "raw_log_tail": self.raw_log[-RAW_LOG_TAIL_CHARS:],
            "error": self.error,
        }
