# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
"""The sweep's steps holding a fact about a tool rather than about the tree.

Each runs a gate showing a fact the tree's configuration or harness is written
on: that Agda reuses an interface whatever its date, what clang-format makes of
``cpp/.clang-format``, what clang-tidy diagnoses under an option, how the JSON
library frees a document.  A gate on an exactly pinned tool runs only when the
branch moves what its fact rests on, and its log says which
(``tools/pin_scope.py``); the clang-format gate, whose tool is pinned to a
range of releases, runs on every run.  Each step sits in the lane whose tree or
toolchain its gate reads, after the steps there that make it.
"""

from __future__ import annotations

from typing import TYPE_CHECKING

from tools._common import CPP_LINT_LANE

if TYPE_CHECKING:
    from tools.run_ci import Runner


def register_tool_fact_steps(runner: Runner) -> None:
    """Register the tool-fact gates, each in the lane that holds what it reads."""
    # Two dumps of the configuration, compile-free and read from the index's
    # file, so the pre-commit tier runs it too.
    runner.step(
        "check-clang-format-config",
        [runner.python, "-m", "tools.check_clang_format_config"],
        cwd=runner.repo_root,
    )
    # In the Agda lane after the Agda gates, whose proof check leaves the
    # interfaces the gate's copy of the project reuses.
    runner.step(
        "check-agda-interface-reuse",
        [runner.python, "-m", "tools.check_agda_interface_reuse"],
        cwd=runner.repo_root,
        lane="agda",
    )
    # In the lane that holds the toolchain's clang-tidy; it reads no database.
    runner.step(
        "check-clang-tidy-facts",
        [runner.python, "-m", "tools.check_clang_tidy_facts"],
        cwd=runner.repo_root,
        lane=CPP_LINT_LANE,
    )
    # In the C++ lane after the test build, whose tree the program is a target of.
    runner.step(
        "check-json-cleanup-abort",
        [runner.python, "-m", "tools.check_json_cleanup_abort"],
        cwd=runner.repo_root,
        lane="cpp",
    )
