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
toolchain its gate reads, after the steps there that make it, and needs the
step whose output it reads.  Four gates hold
a fact about a mutation tool, what Mull's plugin emits and withholds, that the
C++ slices union to the whole tree's census, how cargo-mutants deals its shards
and what mutmut cannot mutate, and run only with the mutation lane, since each
needs its lane's tool.
"""

from __future__ import annotations

import shlex
from typing import TYPE_CHECKING

from tools._common import BUILD_STEP, CPP_CONFIGURE_STEP, CPP_LINT_LANE, GateName

if TYPE_CHECKING:
    from tools.run_ci import Runner

# The step every binding's mutation sweep runs as, whose reports the census
# gate compares and whose trees the Mull gate reads; its lane is the one those
# gates' steps join.
MUTATION_STEP = "mutation testing"
# The census gate's first step, whose census its second compares.
CENSUS_BUILD_STEP = GateName("check-cpp-slices-census-build")


def register_tool_fact_steps(runner: Runner) -> None:
    """Register the tool-fact gates, each in the lane that holds what it reads."""
    # Two dumps of the configuration, compile-free and read from the index's
    # file, so the pre-commit tier runs it too.
    runner.step(
        "check-clang-format-config",
        [runner.python, "-m", "tools.check_clang_format_config"],
        cwd=runner.repo_root,
    )
    # In the Agda lane, whose checker it runs; it checks a copy of the sources,
    # which writes interfaces of its own, so it needs no step.
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
    # In the C++ lane, needing the configure of the test tree, which the gate
    # builds the program in as one of its targets.
    runner.step(
        "check-json-cleanup-abort",
        [runner.python, "-m", "tools.check_json_cleanup_abort"],
        cwd=runner.repo_root,
        lane="cpp",
        needs=(CPP_CONFIGURE_STEP,),
    )


def register_mutation_fact_steps(runner: Runner) -> None:
    """Register the gates on the mutation tools, only when the mutation lane is on.

    Each needs the tool its lane installs, so none can run where the lane does
    not; and each decides from the branch's diff whether its fact could have
    moved, so a sweep whose branch leaves the pins alone pays nothing for them.
    """
    if not runner.opts.lanes.mutation:
        return
    # The shard counts the Rust runner deals partition cargo-mutants' listing.
    runner.step(
        "check-cargo-mutants-shards",
        [runner.python, "-m", "tools.check_cargo_mutants_shards"],
        cwd=runner.repo_root,
        lane="rust",
    )
    # The constructs the pinned mutmut has no operator for, which the Python
    # lane's record carries whole.
    runner.step(
        "check-mutmut-operators",
        [runner.python, "-m", "tools.check_mutmut_operators"],
        cwd=runner.repo_root,
        lane="python",
    )
    # The three slices' union is the whole tree's census.  Both steps follow
    # the sweep in its own lane, because the sweep empties the commit's
    # artifact directory before writing the slice reports there: the census
    # of the unsliced tree is written beside them, then compared with them.
    # The census's dry run runs the unmutated tests, which load the library the
    # build writes; and the sweep runs whenever the build passed, whatever it
    # then answers, so needing the build is needing the sweep to have emptied
    # the directory.  The comparison needs the census, and not a sweep that
    # passed, and refuses a report that is missing, naming it.
    # The directory is named as the sweep names it, by the short hash of HEAD.
    mutation = [step.lane for step in runner.registered_steps if step.name == MUTATION_STEP]
    if len(mutation) != 1:
        msg = f"{MUTATION_STEP!r} must be registered exactly once before the gates following it"
        raise RuntimeError(msg)
    # What the plugin built from the pinned Mull emits, and what it withholds,
    # read with the compile commands of a mutation tree the C++ sweep
    # configures: in the sweep's lane, after it.  It needs the sweep to have
    # run, not to have passed, and the sweep runs whenever the build passed, so
    # it needs the build; it refuses a tree that is not there.
    runner.step(
        "check-mull-plugin-facts",
        [runner.python, "-m", "tools.check_mull_plugin_facts"],
        cwd=runner.repo_root,
        lane=mutation[0],
        needs=(BUILD_STEP,),
    )
    runner.step(
        CENSUS_BUILD_STEP,
        [runner.python, "-m", "tools.check_cpp_slices_census", "--census"],
        cwd=runner.repo_root,
        lane=mutation[0],
        needs=(BUILD_STEP,),
    )
    runner.step(
        "check-cpp-slices-census",
        f"{shlex.quote(runner.python)} -m tools.check_cpp_slices_census"
        + " --compare benchmarks/mutation/$(git rev-parse --short HEAD)",
        cwd=runner.repo_root,
        lane=mutation[0],
        needs=(CENSUS_BUILD_STEP,),
    )
