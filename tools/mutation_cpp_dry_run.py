# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
"""A dry run of one leg of the C++ mutation lane, over the tree as the lane built it.

A dry run runs the leg's unmutated test binary once and reports every mutant
the binary carries without running one, which is the surface a sweep of the
leg would cover.  It runs the lane's own command, in the lane's directory and
environment, and reads the tree the lane built without building it.
"""

from __future__ import annotations

import subprocess
from typing import TYPE_CHECKING

from tools.mutation_cpp import (
    CPP_TEST_TARGET,
    cpp_lane_command,
    cpp_sweep_directory,
    cpp_sweep_environment,
)
from tools.mutation_cpp_legs import CppLeg

from aletheia.common_types import Prose

if TYPE_CHECKING:
    from pathlib import Path

# The runner the lane names. Read here rather than searched for, so a reader
# without it is told what is missing instead of running another one.
MULL_RUNNER = "mull-runner-23"


def leg_build_dir(leg: CppLeg) -> Path:
    """Name the directory one leg builds the tree in."""
    return cpp_sweep_directory() / leg.directory


def lane_binary() -> Path:
    """Name the whole tree's test binary, which the runner runs once per mutant."""
    return leg_build_dir(CppLeg()) / CPP_TEST_TARGET


def dry_run_report(leg: CppLeg, report_dir: Path) -> Path | Prose:
    """Run the lane's command over one leg as a dry run, and name the Elements report it wrote.

    Whether the runner ran is read from the report it wrote, not from its
    exit status.
    """
    build_dir = leg_build_dir(leg)
    _ = subprocess.run(
        cpp_lane_command(MULL_RUNNER, build_dir, report_dir, leg, dry_run=True),
        cwd=cpp_sweep_directory(),
        env=cpp_sweep_environment(leg, build_dir).variables(),
        check=False,
        capture_output=True,
    )
    report = report_dir / f"{leg.report_name}.json"
    if report.is_file():
        return report
    return Prose(f"the dry run of the {leg} leg wrote no {report.name}")
