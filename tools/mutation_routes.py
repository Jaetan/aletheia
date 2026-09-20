# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
"""The kill-route census of a Mull sweep.

Mull's SQLite report keeps, per mutant, the execution status, the exit
status and the test binary's own output. This reads from those what ended
each run, so that a kill by a test's assertion is told from one by a leak
the sanitizer reported, the kernel ending the process, or a fault: a signal,
or an abort from a precondition the standard library checks at the mutation
build's optimisation level and the shipped build does not. A mutant several
lanes killed is attributed to the first of those routes it took in any lane.
"""

from __future__ import annotations

import contextlib
import re
import sqlite3
from typing import TYPE_CHECKING

if TYPE_CHECKING:
    from pathlib import Path

# Mull's execution statuses, as its SQLite report numbers them: a run whose
# tests all passed, and one the runner ended at the timeout.
MULL_PASSED = 2
MULL_TIMEDOUT = 3

# Catch2 reports each failure as a block opened at the site's line and closed
# by the next block or rule. A fatal signal inside a test case is reported the
# same way, with the condition named, and is not the test's own verdict.
_FAILED_BLOCK = re.compile(
    r"^\S+:\d+: FAILED:\n(.*?)(?=^\S+:\d+: FAILED:|^-{10,}$|^={10,}$|\Z)",
    re.MULTILINE | re.DOTALL,
)
_FATAL_CONDITION = "due to a fatal error condition"
# The kernel ending the process, from the shim's own error path.
_KERNEL_ENDED = re.compile(r"^aletheia: ", re.MULTILINE)
_LEAK_REPORTED = "LeakSanitizer: detected memory leaks"

# The routes a kill is read by, in the order a mutant killed by several lanes
# is attributed: a test's assertion first, since that is the one the suite
# would give without any instrument.
KILL_ROUTES: tuple[str, ...] = ("test", "leak", "kernel", "fault", "timeout", "survived")


def kill_route(execution_status: int, stdout: str, stderr: str) -> str:
    """Read what ended one lane's run of one mutant.

    ``test``: an assertion failed, whatever ended the process after it;
    ``leak``: LeakSanitizer reported a leak;
    ``kernel``: the kernel ended the process from its own error path;
    ``fault``: the process died another way, by a signal or an abort from a
    precondition the standard library checks at this build's optimisation
    level; ``timeout``: the runner ended it; ``survived``: every test passed.
    A block Catch2 reports for an exception a test did not expect is an
    assertion's kill here: the behaviour is defined and the test reported it.
    """
    if execution_status == MULL_PASSED:
        return "survived"
    if execution_status == MULL_TIMEDOUT:
        return "timeout"
    if any(_FATAL_CONDITION not in block for block in _FAILED_BLOCK.findall(stdout)):
        return "test"
    if _LEAK_REPORTED in stderr:
        return "leak"
    if _KERNEL_ENDED.search(stderr):
        return "kernel"
    return "fault"


def lane_routes(sqlite_path: Path) -> dict[str, str]:
    """Read each mutant's route from one lane's SQLite report."""
    with contextlib.closing(sqlite3.connect(sqlite_path)) as conn:
        rows = conn.execute("SELECT mutant_id, execution_status, stdout, stderr FROM mutant")
        return {
            str(mutant_id): kill_route(int(status), str(stdout or ""), str(stderr or ""))
            for mutant_id, status, stdout, stderr in rows
        }


def merge_routes(lanes: list[dict[str, str]]) -> dict[str, int]:
    """Count the mutants by route across the lanes, attributed in the order of ``KILL_ROUTES``."""
    counts: dict[str, int] = dict.fromkeys(KILL_ROUTES, 0)
    ids = {mutant for lane in lanes for mutant in lane}
    for mutant in ids:
        routes = {lane[mutant] for lane in lanes if mutant in lane}
        counts[next(route for route in KILL_ROUTES if route in routes)] += 1
    return counts
