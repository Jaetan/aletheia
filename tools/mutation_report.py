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

import collections
from dataclasses import dataclass
from pathlib import Path
from typing import TYPE_CHECKING, NotRequired, TypedDict, cast

import yaml

if TYPE_CHECKING:
    from tools._common import RelPath

REPO_ROOT = Path(__file__).resolve().parent.parent
SPEC_PATH = REPO_ROOT / "docs" / "MUTATION_BENCH.yaml"

# Last ``raw_log`` characters kept in the archived JSON (full log lands in the
# per-binding ``<binding>.raw.txt`` artifact alongside it).
RAW_LOG_TAIL_CHARS = 2000


class LedgerRow(TypedDict):
    """One recorded survivor: its mutator, file, source line and multiplicity."""

    mutator: str
    file: str
    text: str
    count: int


class UnobservedRow(TypedDict):
    """One recorded kill no test observes by behaviour.

    Its mutator, file and source line identify it as a survivor's row does;
    ``route`` says whether the standard library's own check ended the run or a
    bare signal did, and ``refused`` is what that check reported, the invariant
    it would not let the program break.
    """

    mutator: str
    file: str
    text: str
    route: str
    refused: str
    count: int


class Baseline(TypedDict):
    """The per-binding baseline block in ``docs/MUTATION_BENCH.yaml``."""

    survivors: NotRequired[int]
    timeout_ceiling: NotRequired[int]
    total_mutants: NotRequired[int]
    # Mutants per repository-relative file, which the C++ slices are cut on.
    mutants_by_file: NotRequired[dict[RelPath, int]]
    score_pct: NotRequired[int]
    run_at: NotRequired[str]
    survivors_ledger: NotRequired[list[LedgerRow]]
    unobserved_ledger: NotRequired[list[UnobservedRow]]


class BindingSpec(TypedDict):
    """One binding's entry under the YAML ``bindings`` mapping."""

    tool: NotRequired[str]
    baseline: NotRequired[Baseline]


class Spec(TypedDict):
    """The top-level shape of ``docs/MUTATION_BENCH.yaml``."""

    bindings: NotRequired[dict[str, BindingSpec]]


def load_spec() -> Spec:
    """Load ``docs/MUTATION_BENCH.yaml`` (per-binding tool / hot_path / baseline).

    Here rather than with the runner, so a lane can read the record without
    importing the module that drives it: the C++ merge reads the census it
    refuses a short union against, and the runner reads the same file to judge
    the survivors.
    """
    return cast("Spec", yaml.safe_load(SPEC_PATH.read_text()))


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
    unrecorded_unobserved_kills: NotRequired[list[UnobservedRow]]
    stale_unobserved_ledger: NotRequired[list[UnobservedRow]]


# A survivor's identity in the ledger: mutator, repository-relative file and
# the text of its source line.  Keyed on the text and not the line number, so
# an edit above the site does not move it, and an edit of the site does.
SurvivorKey = tuple[str, str, str]

# An unobserved kill's identity: a survivor's three, then the route it took and
# what the check refused.  The route and the refusal are part of the identity
# because they are the diagnosis the row exists to carry, and a line that loses
# one check and gains another is a different claim about the same line.
UnobservedKey = tuple[str, str, str, str, str]


def unobserved_rows_to_ledger(rows: dict[UnobservedKey, int]) -> list[UnobservedRow]:
    """Render unobserved kills in the ledger's row shape, sorted by identity.

    Here rather than with the runner, because the lane writes the same shape
    into its artifact as the runner compares against the record, and a second
    spelling of it is a second thing to keep true.
    """
    return [
        {
            "mutator": mutator,
            "file": file,
            "text": text,
            "route": route,
            "refused": refused,
            "count": count,
        }
        for (mutator, file, text, route, refused), count in sorted(rows.items())
    ]


def unobserved_ledger_to_rows(ledger: list[UnobservedRow]) -> dict[UnobservedKey, int]:
    """Read a ledger back into unobserved kills keyed by identity."""
    rows: dict[UnobservedKey, int] = collections.Counter()
    for row in ledger:
        rows[(row["mutator"], row["file"], row["text"], row["route"], row["refused"])] += row[
            "count"
        ]
    return rows


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
        """Materialize for JSON archival; keeps the last ``RAW_LOG_TAIL_CHARS`` of the log."""
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
