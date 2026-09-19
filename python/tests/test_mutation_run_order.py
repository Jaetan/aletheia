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

from tools.mutation_run import cpp_lane_command


def _command() -> list[str]:
    """Build one lane's argv, the paths being the only thing it reads."""
    return cpp_lane_command("mull-runner-23", Path("cpp/build-mutation"), Path("artifacts"), "")


def test_the_lane_hands_the_binary_a_pinned_order() -> None:
    """The argv ends with the separator and the declaration order behind it."""
    assert _command()[-3:] == ["--", "--order", "decl"]


def test_every_runner_option_stays_ahead_of_the_separator() -> None:
    """Mull parses what precedes the separator; only Catch2 reads what follows."""
    argv = _command()
    separator = argv.index("--")
    assert all(arg.startswith("--report") for arg in argv[2:separator])
    assert "--order" not in argv[:separator]
