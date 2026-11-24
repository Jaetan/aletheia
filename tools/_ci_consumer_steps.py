# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
"""The sweep's steps building a binding's consumer as a user would.

The installed C++ package is found with ``find_package`` by a project of its
own, which links and runs the client and both loaders
(``tools/check_cpp_installed_consumer.py``), and the bundle validator's Go, C++
and Rust consumers are built against the tree's bindings
(``tools/check_bundle_consumers.py``), each in its binding's lane.  Each runs
where the branch moves what it reads, and says so either way.
"""

from __future__ import annotations

from typing import TYPE_CHECKING

from tools._common import CPP_CONFIGURE_STEP

if TYPE_CHECKING:
    from tools.run_ci import Runner


def register_consumer_steps(runner: Runner) -> None:
    """Register the consumer gates, each in the lane of its binding."""
    # The installed package needs the configure of the test tree, which fetched
    # the sources the gate builds the package from.
    runner.step(
        "check-cpp-installed-consumer",
        [runner.python, "-m", "tools.check_cpp_installed_consumer"],
        cwd=runner.repo_root,
        lane="cpp",
        needs=(CPP_CONFIGURE_STEP,),
    )
    # The bundle validator's consumers read the bindings' sources alone.
    for binding, lane in (("go", "misc"), ("cpp", "cpp"), ("rust", "rust")):
        runner.step(
            f"check-bundle-consumer-{binding}",
            [runner.python, "-m", "tools.check_bundle_consumers", "--binding", binding],
            cwd=runner.repo_root,
            lane=lane,
        )
