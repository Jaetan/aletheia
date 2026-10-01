# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
"""The static gate holds each C++ tree's slice weights to the files a slice can claim.

Four arms, and none can be exercised by the tree as it stands, which is the
reason they are tested here rather than trusted: a tree the record weighs
nothing for, a record for a tree the lane does not build, a recorded weight
for a file no slice can claim, and a partition that does not cover its domain
exactly once.  The last guards the invariant every refusal in the lane is
written against, and `partition` satisfies it by construction, so the only way
to know the arm would speak is to give it a partition that does not.
"""

from __future__ import annotations

from typing import TYPE_CHECKING, Literal

from tools import check_mutation_setup
from tools._common import RelPath
from tools.mutation_cpp_legs import CppTree
from tools.mutation_cpp_slices import CPP_SLICES, SuiteRuns
from tools.mutation_report import load_spec

if TYPE_CHECKING:
    from collections.abc import Sequence

    import pytest

    from tools.mutation_cpp_legs import CppTreeName
    from tools.mutation_cpp_slices import Slice, SliceWeights, TreeRuns

# A key the record may hold: a tree the lane builds, or one it does not.
type RecordedTree = CppTreeName | Literal["thread"]

# A file every tree's slices can claim, weighed in each.
_CLAIMABLE: TreeRuns = {RelPath("cpp/src/client.cpp"): SuiteRuns(1.0)}


def _recorded() -> dict[str, object]:
    """Read the bindings the repository actually records."""
    return dict(load_spec().get("bindings", {}))


def _bindings(runs: dict[RecordedTree, TreeRuns]) -> dict[str, object]:
    """Build the shape the gate reads each tree's recorded weights out of."""
    return {"cpp": {"baseline": {"runs_by_file": runs}}}


def _every_tree(changed: dict[CppTreeName, TreeRuns] | None = None) -> dict[RecordedTree, TreeRuns]:
    """Weigh every tree the lane builds, a tree named in ``changed`` with the weights given."""
    given = changed or {}
    return {tree.key: given.get(tree.key, dict(_CLAIMABLE)) for tree in CppTree}


def test_the_recorded_weights_are_files_a_slice_can_claim() -> None:
    """Every tree is weighed, each over files of the derived domain alone, as the tree stands."""
    assert check_mutation_setup.cpp_slice_weights_are_of_the_domain(_recorded()) == []


def test_a_tree_weighed_for_nothing_is_caught() -> None:
    """A tree the record leaves out would be cut on nothing, every file weighing the same."""
    runs = _every_tree()
    del runs[CppTree.ADDRESS.key]
    failures = check_mutation_setup.cpp_slice_weights_are_of_the_domain(_bindings(runs))
    assert len(failures) == 1
    assert "records nothing for the address tree" in failures[0]


def test_a_record_for_no_tree_the_lane_builds_is_caught() -> None:
    """A tree renamed or retired keeps its weights, which no leg reads."""
    runs = _every_tree()
    runs["thread"] = dict(_CLAIMABLE)
    failures = check_mutation_setup.cpp_slice_weights_are_of_the_domain(_bindings(runs))
    assert len(failures) == 1
    assert "names thread, which is no tree" in failures[0]


def test_a_weight_for_a_file_no_slice_can_claim_is_caught() -> None:
    """A renamed or held-out file keeps its weight in its tree, and it counts toward no slice."""
    stray: TreeRuns = {**_CLAIMABLE, RelPath("cpp/src/renamed_away.cpp"): SuiteRuns(7.0)}
    failures = check_mutation_setup.cpp_slice_weights_are_of_the_domain(
        _bindings(_every_tree({"leak": stray})),
    )
    assert len(failures) == 1
    assert "cpp/src/renamed_away.cpp" in failures[0]
    assert "in the leak tree" in failures[0]
    assert "counts toward no slice" in failures[0]


def test_a_partition_that_drops_a_file_is_caught(monkeypatch: pytest.MonkeyPatch) -> None:
    """The arm that cannot fire against the real partition fires, per tree, on one dropping a file.

    A file in no slice is mutated by every slice, which the merge refuses by
    identity; this arm is what says so before a sweep is spent finding out.
    """

    def dropping(
        domain: Sequence[RelPath], _weights: SliceWeights, slices: int = CPP_SLICES
    ) -> tuple[Slice, ...]:
        kept = tuple(domain)[1:]
        return (*(() for _ in range(slices - 1)), tuple(kept))

    monkeypatch.setattr(check_mutation_setup, "partition", dropping)
    failures = check_mutation_setup.cpp_slice_weights_are_of_the_domain(_recorded())
    assert len(failures) == len(CppTree)
    assert all("partition claims" in failure for failure in failures)


def test_a_partition_that_claims_a_file_twice_is_caught(monkeypatch: pytest.MonkeyPatch) -> None:
    """The other half of exactly once: a file two slices both sweep."""

    def doubling(
        domain: Sequence[RelPath], _weights: SliceWeights, slices: int = CPP_SLICES
    ) -> tuple[Slice, ...]:
        whole = tuple(domain)
        return (*(() for _ in range(slices - 2)), whole[:1], whole)

    monkeypatch.setattr(check_mutation_setup, "partition", doubling)
    failures = check_mutation_setup.cpp_slice_weights_are_of_the_domain(_recorded())
    assert len(failures) == len(CppTree)
    assert all("partition claims" in failure for failure in failures)
