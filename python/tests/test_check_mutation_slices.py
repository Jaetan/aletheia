# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
"""The static gate holds the C++ slice weights to the files a slice can claim.

Two arms, and neither can be exercised by the tree as it stands, which is the
reason they are tested here rather than trusted: a recorded weight for a file
no slice can claim, and a partition that does not cover its domain exactly
once.  The second guards the invariant every refusal in the lane is written
against, and `partition` satisfies it by construction, so the only way to know
the arm would speak is to give it a partition that does not.
"""

from __future__ import annotations

from typing import TYPE_CHECKING

from tools import check_mutation_setup
from tools.mutation_cpp_slices import CPP_SLICES
from tools.mutation_report import load_spec

if TYPE_CHECKING:
    from collections.abc import Sequence

    import pytest

    from tools._common import RelPath
    from tools.mutation_cpp_slices import MutantCounts, Slice


def _recorded() -> dict[str, object]:
    """Read the bindings the repository actually records."""
    return dict(load_spec().get("bindings", {}))


def _bindings(counts: dict[str, int]) -> dict[str, object]:
    """Build the shape the gate reads a binding's recorded census out of."""
    return {"cpp": {"baseline": {"mutants_by_file": counts}}}


def test_the_recorded_weights_are_files_a_slice_can_claim() -> None:
    """Every recorded file is in the derived domain, which is what the tree says today."""
    assert check_mutation_setup.cpp_slice_weights_are_of_the_domain(_recorded()) == []


def test_a_weight_for_a_file_no_slice_can_claim_is_caught() -> None:
    """A renamed or held-out file keeps its weight and it counts toward no slice."""
    failures = check_mutation_setup.cpp_slice_weights_are_of_the_domain(
        _bindings({"cpp/src/renamed_away.cpp": 7}),
    )
    assert len(failures) == 1
    assert "cpp/src/renamed_away.cpp" in failures[0]
    assert "counts toward no slice" in failures[0]


def test_a_partition_that_drops_a_file_is_caught(monkeypatch: pytest.MonkeyPatch) -> None:
    """The arm that cannot fire against the real partition fires against one that drops a file.

    A file in no slice is mutated by every slice, which the merge refuses by
    identity; this arm is what says so before a sweep is spent finding out.
    """

    def dropping(
        domain: Sequence[RelPath], _weights: MutantCounts, slices: int = CPP_SLICES
    ) -> tuple[Slice, ...]:
        kept = tuple(domain)[1:]
        return (*(() for _ in range(slices - 1)), tuple(kept))

    monkeypatch.setattr(check_mutation_setup, "partition", dropping)
    failures = check_mutation_setup.cpp_slice_weights_are_of_the_domain(_recorded())
    assert len(failures) == 1
    assert "the partition claims" in failures[0]


def test_a_partition_that_claims_a_file_twice_is_caught(monkeypatch: pytest.MonkeyPatch) -> None:
    """The other half of exactly once: a file two slices both sweep."""

    def doubling(
        domain: Sequence[RelPath], _weights: MutantCounts, slices: int = CPP_SLICES
    ) -> tuple[Slice, ...]:
        whole = tuple(domain)
        return (*(() for _ in range(slices - 2)), whole[:1], whole)

    monkeypatch.setattr(check_mutation_setup, "partition", doubling)
    failures = check_mutation_setup.cpp_slice_weights_are_of_the_domain(_recorded())
    assert len(failures) == 1
    assert "the partition claims" in failures[0]
