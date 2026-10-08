# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
"""The shapes the mutation runner and its per-binding lanes share.

``MutationReport`` is one binding's result, serialized to ``<binding>.json``
under the run's artifact directory; the ``TypedDict`` classes are the shape of
``docs/MUTATION_BENCH.yaml`` and of the drift verdict written to
``summary.json``.  They live apart from the runner so the C++ lane
(``tools/mutation_cpp.py``) can build a report without importing the module
that drives it; ``scratch_tree_or_report`` is here for the same reason, the
Go and Rust lanes both sweeping a copy of the tree.
"""

from __future__ import annotations

import collections
import contextlib
from dataclasses import dataclass
from pathlib import Path
from typing import TYPE_CHECKING, Literal, NewType, NotRequired, TypedDict, cast

import yaml

from tools._common import RelPath, scratch_worktree

if TYPE_CHECKING:
    from collections.abc import Generator

    from tools.mutation_cpp_slices import FileRuns

REPO_ROOT = Path(__file__).resolve().parent.parent
SPEC_PATH = REPO_ROOT / "docs" / "MUTATION_BENCH.yaml"

# Last ``raw_log`` characters kept in the archived JSON (full log lands in the
# per-binding ``<binding>.raw.txt`` artifact alongside it).
RAW_LOG_TAIL_CHARS = 2000

# A number of mutants: a census's, a bucket's or a file's.
MutantCount = NewType("MutantCount", int)

# A route a C++ kill took, one of ``KILL_ROUTES`` in ``tools/mutation_routes.py``.
KillRoute = NewType("KillRoute", str)

# The C++ census: how many mutants each route ended.
type RouteCensus = dict[KillRoute, MutantCount]

# A binding's verdict.  ``ok``: the run and the record agree.  ``regression``:
# the run is worse than the record.  ``stale``: the run is better, and the
# change that made it so lowers the record.  Both fail the lane, and a run worse
# somewhere is a regression whatever else it improved.  ``first_run``: the
# record holds no count yet.  ``leg``: one part of a sweep, which the merge
# judges.  ``error``: the run gave no verdict.
DriftStatus = Literal["ok", "regression", "stale", "first_run", "leg", "error"]


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
    # The suite runs each repository-relative file's C++ mutants cost, which
    # the lane's slices are cut on.
    runs_by_file: NotRequired[FileRuns]
    score_pct: NotRequired[int]
    run_at: NotRequired[str]
    survivors_ledger: NotRequired[list[LedgerRow]]
    unobserved_ledger: NotRequired[list[UnobservedRow]]
    # Mutants on lines no test executes, where the tool has that bucket: the
    # count, and a ledger of the lines coverage cannot attribute to a test, a
    # package-level constant being the case.  A run's not-covered mutant the
    # ledger does not name is a line that lost its test.
    not_covered: NotRequired[int]
    not_covered_ledger: NotRequired[list[LedgerRow]]
    # Every mutant the tool made, whatever became of it, where it puts some in
    # buckets beyond killed, survived and timed out, which no other count reads.
    generated: NotRequired[MutantCount]
    kill_routes: NotRequired[RouteCensus]


class BindingSpec(TypedDict):
    """One binding's entry under the YAML ``bindings`` mapping."""

    tool: NotRequired[str]
    # The files the lane must carry a mutant in, each repository-relative.
    hot_path: NotRequired[list[RelPath]]
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

    status: DriftStatus
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
    observed_not_covered: NotRequired[int]
    baseline_not_covered: NotRequired[int]
    unrecorded_not_covered: NotRequired[list[LedgerRow]]
    stale_not_covered_ledger: NotRequired[list[LedgerRow]]
    observed_total_mutants: NotRequired[MutantCount]
    baseline_total_mutants: NotRequired[MutantCount]
    observed_generated: NotRequired[MutantCount | None]
    baseline_generated: NotRequired[MutantCount]
    observed_kill_routes: NotRequired[RouteCensus]
    baseline_kill_routes: NotRequired[RouteCensus]
    hot_path_without_mutants: NotRequired[list[RelPath]]


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


@dataclass(frozen=True)
class Observed:
    """What a run reports beyond its kills and survivors, each ``None`` where its tool has none.

    ``timeouts``: the mutants the tool started and could not finish, neither
    killed nor survived, so a run that timed out on nearly everything reports
    no survivors and full efficacy; the drift gate reads this to refuse such
    a run.  ``generated``: every mutant the tool made, where it puts some in
    buckets beyond killed, survived and timed out, so a mutant that left the
    surface for one of those moves a count.  ``routes``: the C++ census by
    kill route.  ``mutated_files``: the files the run made a mutant in.
    """

    timeouts: int | None = None
    generated: MutantCount | None = None
    routes: RouteCensus | None = None
    mutated_files: frozenset[RelPath] | None = None


@dataclass
class MutationReport:
    """Per-binding mutation result; serialized to ``<binding>.json``."""

    binding: str
    tool: str
    killed: int
    survived: int
    raw_log: str
    error: str | None = None
    observed: Observed = Observed()

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
            "timeouts": self.observed.timeouts,
            "generated": self.observed.generated,
            "routes": self.observed.routes,
            "mutated_files": (
                None if self.observed.mutated_files is None else sorted(self.observed.mutated_files)
            ),
            "score_pct": self.score_pct,
            "raw_log_tail": self.raw_log[-RAW_LOG_TAIL_CHARS:],
            "error": self.error,
        }


@contextlib.contextmanager
def scratch_tree_or_report(
    repo_root: Path, binding: Literal["go", "rust"], tool: Literal["gremlins", "cargo-mutants"]
) -> Generator[Path | MutationReport]:
    """Yield a scratch copy of ``repo_root`` (``scratch_worktree``), or the lane's refusal.

    A lane that sweeps a copy has no sweep without one, so where the copy
    cannot be made this yields the binding's report saying why in its place.
    Only the copying is caught: an error raised in the ``with`` body propagates.
    """
    with contextlib.ExitStack() as stack:
        try:
            tree = stack.enter_context(scratch_worktree(repo_root))
        except RuntimeError as exc:
            yield MutationReport(
                binding, tool, 0, 0, "", error=f"no scratch copy of the tree: {exc}"
            )
            return
        yield tree
