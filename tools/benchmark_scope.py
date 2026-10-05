# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
"""Whether a benchmark lane measures, asked before the lane installs a toolchain.

A benchmark lane builds and measures all four bindings and the kernel they
load, so it measures when the diff vs ``main`` could move any of them: the
reading of the diff ``tools/mutation_run.py`` scopes its sweeps by
(``bindings_in_scope``), asked once with this lane's own global paths.  A
change to the kernel, the benchmark harness, its schema, this gate, this
question or the workflow itself measures everything; a change confined to a
binding's directory measures too, the lanes running every binding together;
a change touching none of them, documentation alone, measures nothing.

The ``load scaling`` leg is a required check, so it never sits behind a
workflow path filter, which would leave it unreported on a pull request it
skips: it always runs, asks this, and passes having measured nothing when the
answer is no.

Run as ``python -m tools.benchmark_scope``.  The answer is written as
``LANE_MEASURES=1`` or ``LANE_MEASURES=0`` to the file ``GITHUB_ENV`` names,
and to stdout where the environment names none.  The decision itself goes to
stderr, so a lane's log states what it measured and why.
"""

from __future__ import annotations

import argparse
import sys
from typing import TYPE_CHECKING

from tools._common import write_workflow_line
from tools.mutation_run import BINDING_DIRS, KERNEL_PATHS, REPO_ROOT, bindings_in_scope

from aletheia.common_types import ExitStatus

if TYPE_CHECKING:
    from pathlib import Path

# The variable a lane's steps read, as `!= '0'`: an answer that did not arrive
# measures, since measuring what nothing moved costs minutes and skipping what
# a change moved lets a regression through a required check.
MEASURES_VAR = "LANE_MEASURES"

# A change under any of these moves every binding's measurement, or the
# measuring itself: the kernel, the harness that drives the four bindings, the
# schema their reports follow, the gate that judges them, this question and
# the workflow running all of it.
BENCHMARK_GLOBAL_PATHS = (
    *KERNEL_PATHS,
    "benchmarks/",
    "tools/benchmark_gate.py",
    "tools/benchmark_scope.py",
    "tools/check_bench_schema.py",
    "tools/mutation_run.py",  # the reading of the diff this question asks
    "tools/_common.py",
    "tools/__init__.py",
    ".github/workflows/benchmark.yml",
)


def lane_measures(repo_root: Path) -> bool:
    """Report whether a benchmark lane measures on the diff of ``repo_root``'s branch vs ``main``.

    ``bindings_in_scope`` returns ``None`` for the cases that run everything (an
    empty diff, a global path, a git error, the escape hatch), and the lane
    measures on it.
    """
    in_scope = bindings_in_scope(
        repo_root, binding_dirs=BINDING_DIRS, global_paths=BENCHMARK_GLOBAL_PATHS
    )
    return in_scope is None or bool(in_scope)


def main() -> ExitStatus:
    """Write this lane's decision where its workflow steps read it."""
    _ = argparse.ArgumentParser(description=__doc__).parse_args()
    measures = lane_measures(REPO_ROOT)
    _ = sys.stderr.write(
        "[benchmark] scope: the diff can move a measurement, so this lane measures\n"
        if measures
        else "[benchmark] scope: the diff moves nothing measured, so this lane measures nothing\n"
    )
    write_workflow_line(f"{MEASURES_VAR}={'1' if measures else '0'}")
    return ExitStatus(0)


if __name__ == "__main__":
    sys.exit(main())
