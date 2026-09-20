# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
"""Tests for ``tools.mutation_run.mull_counts``, the reader of a C++ lane's log.

Mull prints a survivor count to its stdout only when something survived; a
lane that killed everything says so in its IDE report alone, with a score of
100 percent and no survivor line. The reader takes the lane's log, which is
the stdout followed by that report, and must read a clean lane as zero
survivors rather than as a log it cannot parse: the first clean C++ sweep
failed the lane for want of a line Mull never prints.
"""

from __future__ import annotations

import pytest

from tools.mutation_run import mull_counts

_PROGRESS = "       [################################] 1140/1140. Finished in 2m59.9s\n"


def test_a_lane_with_survivors_reads_its_count() -> None:
    """The survivor line on stdout is the count, and the total comes from the progress tail."""
    raw = _PROGRESS + "[info] Mutation score: 99%\n[info] Surviving mutants: 6\n"
    assert mull_counts(raw) == (1134, 6)


def test_a_clean_lane_reads_zero_from_its_report() -> None:
    """No survivor line, and the report saying every mutant died, is zero survivors."""
    raw = _PROGRESS + "[info] Mutation score: 100%\n[info] All mutations have been killed\n"
    assert mull_counts(raw) == (1140, 0)


@pytest.mark.parametrize(
    "raw",
    [
        "",
        _PROGRESS,
        "[info] Total execution time: 3m6.6s\n",
    ],
)
def test_a_log_without_a_summary_is_not_a_count(raw: str) -> None:
    """A run that never said what survived is not a count, nor is a progress line alone."""
    assert mull_counts(raw) is None
