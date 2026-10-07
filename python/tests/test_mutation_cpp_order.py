# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
"""The C++ lane pins the test order it sweeps under.

Catch2 shuffles its cases by default under a seed that changes every run, and
mull runs the test binary once per mutant, so an unpinned lane reads a
different kill-route census every sweep: two pinned sweeps of one tree agreed
on every mutant, where two shuffled ones read the fault route at 98 and 99
against the pinned 93. A fault ends the process, so the order decides which
test reports before the run stops. The recorded census is therefore taken
under a stated order, which is what makes it a measurement rather than one
sample of a shuffle. That the verdict itself holds under every order is a
separate property, which a probe sweeps several orders to hold.

A run also ends at its first failing assertion, which moves no route: the
census reads any failing assertion as the test's kill, and a run with none
goes through the whole suite either way. A probe sweeps without the flag to
hold that.
"""

from __future__ import annotations

import os
from pathlib import Path
from typing import NewType

import pytest

from tools.mutation_cpp import (
    CPP_BUILD_JOBS_CAP,
    CPP_MUTANT_CAP_MS,
    LANE_RUN,
    CaseOrder,
    CppRun,
    RngSeed,
    cpp_build_command,
    cpp_lane_command,
)
from tools.mutation_cpp_legs import CppLeg, CppTree

# The binary's own words behind the separator, joined by spaces.
_Spelling = NewType("_Spelling", str)


def _command(run: CppRun = LANE_RUN) -> list[str]:
    """Build one leg's argv as ``run`` asks, the paths being the only thing it reads."""
    leg = CppLeg(CppTree.PLAIN, 1)
    return cpp_lane_command(
        "mull-runner-23", Path("cpp") / leg.directory, Path("artifacts"), leg, run
    )


def test_the_lane_hands_the_binary_a_pinned_order() -> None:
    """The binary's argv, behind the separator, opens with the declaration order."""
    argv = _command()
    separator = argv.index("--")
    assert argv[separator + 1 : separator + 3] == ["--order", "decl"]


def test_a_run_ends_at_its_first_failing_assertion() -> None:
    """The binary is told to stop at the first failure rather than run the rest of the suite."""
    argv = _command()
    assert "--abort" in argv[argv.index("--") + 1 :]


@pytest.mark.parametrize(
    ("order", "spelled"),
    [
        pytest.param(CaseOrder("lex"), _Spelling("--order lex --abort"), id="lex"),
        pytest.param(
            CaseOrder("rand", RngSeed(4919)),
            _Spelling("--order rand --rng-seed 4919 --abort"),
            id="rand",
        ),
    ],
)
def test_another_order_replaces_the_pinned_one_and_nothing_else(
    order: CaseOrder, spelled: _Spelling
) -> None:
    """A probe's order, its seed with it, stands where the lane's does; every other word stays."""
    lane, varied = _command(), _command(CppRun(order=order))
    separator = lane.index("--")
    assert varied[: separator + 1] == lane[: separator + 1]
    assert " ".join(varied[separator + 1 :]) == spelled


def test_a_run_not_ending_at_its_first_failure_drops_only_the_flag() -> None:
    """Without the ending, the argv is the lane's less ``--abort``."""
    lane = _command()
    lane.remove("--abort")
    assert _command(CppRun(abort=False)) == lane


def test_every_runner_option_stays_ahead_of_the_separator() -> None:
    """Mull parses what precedes the separator; only Catch2 reads what follows."""
    argv = _command()
    separator = argv.index("--")
    assert all(arg.startswith("--") for arg in argv[2:separator])
    assert "--order" not in argv[:separator]
    assert "--abort" not in argv[:separator]


def test_a_dry_run_is_the_lane_s_argv_with_the_runner_told_to_run_no_mutant() -> None:
    """The one runner option a dry run adds sits ahead of the separator; nothing else moves."""
    dry = _command(CppRun(dry_run=True))
    assert "--dry-run" not in _command()
    assert dry.index("--dry-run") < dry.index("--")
    dry.remove("--dry-run")
    assert dry == _command()


def test_the_cap_per_mutant_is_the_runner_s_minimum_timeout() -> None:
    """The knob that raises Mull's ten-times-the-baseline, ahead of the separator.

    The cap on the unmutated runs is the configuration's, which every
    invocation inherits, so the command line carries no ``--timeout``.
    """
    argv = _command()
    assert f"--minimum-timeout={CPP_MUTANT_CAP_MS}" in argv[: argv.index("--")]
    assert not any(arg.startswith("--timeout") for arg in argv)


def test_the_mutation_build_compiles_several_units_at_once(tmp_path: Path) -> None:
    """The build carries a parallel count, bounded so the plugin compiles fit in memory."""
    argv = cpp_build_command("cmake", tmp_path)
    assert argv[:5] == ["cmake", "--build", str(tmp_path), "--target", "unit_tests"]
    assert argv[5] == "--parallel"
    assert 1 <= int(argv[6]) <= CPP_BUILD_JOBS_CAP


def test_the_mutation_build_counts_the_cpus_it_was_given(
    monkeypatch: pytest.MonkeyPatch, tmp_path: Path
) -> None:
    """Under the cap, a build given three CPUs of the machine's 24 runs three compiles."""
    monkeypatch.setattr(os, "cpu_count", lambda: 24)
    monkeypatch.setattr(os, "process_cpu_count", lambda: 3)
    assert cpp_build_command("cmake", tmp_path)[5:7] == ["--parallel", "3"]
