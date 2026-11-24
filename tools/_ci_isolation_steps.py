# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
"""The sweep's steps running each Go, C++ and Rust test alone.

``tools/check_tests_alone.py`` runs every test of a binding in a process of its
own, where a test leaning on another having run first fails every time, in the
lane of its binding and after the build its test binaries come from.  Each runs
where the branch moves its binding, and says so either way.
"""

from __future__ import annotations

from typing import TYPE_CHECKING, NamedTuple

from tools._common import (
    BUILD_STEP,
    CARGO_TEST_BUILD_STEP,
    CPP_BUILD_STEP,
    EXCEL_CARGO_TEST_BUILD_STEP,
    GateName,
)
from tools._run_ci_options import LaneName

if TYPE_CHECKING:
    from tools.check_tests_alone import Binding
    from tools.run_ci import Runner


class AloneStep(NamedTuple):
    """Where a binding's alone run goes: its lane, and the steps its test binaries come from."""

    lane: LaneName
    needs: tuple[GateName, ...]


STEPS: dict[Binding, AloneStep] = {
    "go": AloneStep(LaneName("misc"), (BUILD_STEP,)),
    "cpp": AloneStep(LaneName("cpp"), (BUILD_STEP, CPP_BUILD_STEP)),
    "rust": AloneStep(
        LaneName("rust"), (BUILD_STEP, CARGO_TEST_BUILD_STEP, EXCEL_CARGO_TEST_BUILD_STEP)
    ),
}


def register_isolation_steps(runner: Runner) -> None:
    """Register each binding's alone run in its lane, after the builds its tests come from."""
    for binding, (lane, needs) in STEPS.items():
        runner.step(
            f"check-tests-alone-{binding}",
            [runner.python, "-m", "tools.check_tests_alone", "--binding", binding],
            cwd=runner.repo_root,
            lane=lane,
            needs=needs,
        )
