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
"""

from __future__ import annotations

from pathlib import Path

from tools.mutation_cpp import (
    CPP_BUILD_JOBS_CAP,
    CPP_MUTANT_CAP_MS,
    CppLeg,
    CppTree,
    cpp_build_command,
    cpp_lane_command,
)


def _command() -> list[str]:
    """Build one leg's argv, the paths being the only thing it reads."""
    leg = CppLeg(CppTree.PLAIN, 1)
    return cpp_lane_command("mull-runner-23", Path("cpp") / leg.directory, Path("artifacts"), leg)


def test_the_lane_hands_the_binary_a_pinned_order() -> None:
    """The argv ends with the separator and the declaration order behind it."""
    assert _command()[-3:] == ["--", "--order", "decl"]


def test_every_runner_option_stays_ahead_of_the_separator() -> None:
    """Mull parses what precedes the separator; only Catch2 reads what follows."""
    argv = _command()
    separator = argv.index("--")
    assert all(arg.startswith("--") for arg in argv[2:separator])
    assert "--order" not in argv[:separator]


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
