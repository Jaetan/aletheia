# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
"""The kill-route census of a Mull sweep.

Mull's SQLite report keeps, per mutant, the execution status, the exit
status and the test binary's own output. This reads from those what ended
each run, so that a kill by a test's assertion is told from one by a leak
the sanitizer reported, a read of memory the program does not own that the
address sanitizer reported, the kernel ending the process, a check the
standard library runs in the mutation build (debug mode's iterator and bounds
checks, and its assertions), or a fault: a signal the process died by. A
mutant several lanes killed is attributed to the first of those routes it
took in any lane.
"""

from __future__ import annotations

import contextlib
import re
import sqlite3
from typing import TYPE_CHECKING, NamedTuple

if TYPE_CHECKING:
    from pathlib import Path

# Mull's execution statuses, as its SQLite report numbers them: a run whose
# tests all passed, and one the runner ended at the timeout. Either is the
# route by itself; every other status is read from the captured output.
MULL_PASSED = 2
MULL_TIMEDOUT = 3
_ROUTE_BY_STATUS = {MULL_PASSED: "survived", MULL_TIMEDOUT: "timeout"}

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
# AddressSanitizer names itself on the first line of every report it ends a
# run with, whatever the class it read: a use after free, a read past an
# allocation, or a read of a frame that has returned. LeakSanitizer's own
# report is read before this one, so a leak under an address tree stays a
# leak rather than becoming an address kill.
_ADDRESS_REPORTED = "ERROR: AddressSanitizer:"
# What the address sanitizer read, the word it names the class by: a use after
# free, a read past an allocation, a read of a frame that has returned. It
# carries no values, so it keys a row the way a check's invariant does.
_ADDRESS_KIND = re.compile(r"ERROR: AddressSanitizer: (\S+)")
# The sanitizers that end a run with a report, in the order a run carrying
# more than one is read by: LeakSanitizer's report is part of what an
# address tree prints at exit, and a leak is a leak wherever it was read.
_SANITIZER_REPORTS: tuple[tuple[str, str], ...] = (
    (_LEAK_REPORTED, "leak"),
    (_ADDRESS_REPORTED, "address"),
)
# libstdc++ reports a failed check on stderr and aborts. Debug mode prints the
# header's path, the function under ``In function:``, then ``Error:`` and what
# the operation attempted, wrapped over lines up to a blank one; the
# lightweight assertions print one line naming the header, the function and
# the expression that failed.
_LIBSTDCXX_CHECK = re.compile(
    r"^In function:\n[\s\S]*?^Error: ([\s\S]+?)\n\n|^\S+:\d+: .*: Assertion '([^']*)' failed\.$",
    re.MULTILINE,
)
# What a check refused is read down to the invariant, dropping the values it
# refused them for: debug mode prints an index and a size into its sentence,
# and those come from the test data, so a fixture the suite feeds differently
# would reword a recorded row without any claim having changed. Every message
# this tree produces carries its values last, after the invariant, and an
# assertion's expression carries none, so the text up to the first number is
# the claim: a subscript refusal reads the same whichever index tripped it.
_CHECK_VALUES = re.compile(r"\s*\d.*\Z", re.DOTALL)

# The routes a kill is read by, in the order a mutant killed by several lanes
# is attributed: a test's assertion first, since that is the one the suite
# would give without any instrument.
KILL_ROUTES: tuple[str, ...] = (
    "test",
    "leak",
    "address",
    "kernel",
    "check",
    "fault",
    "timeout",
    "survived",
)


def kill_route(execution_status: int, stdout: str, stderr: str) -> str:
    """Read what ended one lane's run of one mutant.

    ``test``: an assertion failed, whatever ended the process after it;
    ``leak``: LeakSanitizer reported a leak; ``address``: AddressSanitizer
    reported a read or a write of memory the program does not own;
    ``kernel``: the kernel ended the process from its own error path;
    ``check``: a check the standard library runs in the mutation build ended
    it, at the read or the subscript it refused; ``fault``: the process died
    another way, by a signal;
    ``timeout``: the runner ended it; ``survived``: every test passed. A block
    Catch2 reports for an exception a test did not expect is an assertion's
    kill here: the behaviour is defined and the test reported it.
    """
    if execution_status in _ROUTE_BY_STATUS:
        return _ROUTE_BY_STATUS[execution_status]
    if any(_FATAL_CONDITION not in block for block in _FAILED_BLOCK.findall(stdout)):
        return "test"
    reported = next((route for marker, route in _SANITIZER_REPORTS if marker in stderr), "")
    if reported:
        return reported
    if _KERNEL_ENDED.search(stderr):
        return "kernel"
    if _LIBSTDCXX_CHECK.search(stderr):
        return "check"
    return "fault"


class Ending(NamedTuple):
    """How one lane's run of one mutant ended: its route, and what the check refused.

    ``refused`` is the invariant the standard library's check reported, the
    one the read or the subscript would have broken, or, where the address
    sanitizer ended the run, the class it names the report by. It is empty for
    every other route. The values a check was refused for are not part of it,
    for the reason at ``_CHECK_VALUES``.
    """

    route: str
    refused: str


def lane_endings(sqlite_path: Path) -> dict[str, Ending]:
    """Read each mutant's ending from one lane's SQLite report."""
    with contextlib.closing(sqlite3.connect(sqlite_path)) as conn:
        rows = conn.execute("SELECT mutant_id, execution_status, stdout, stderr FROM mutant")
        return {
            str(mutant_id): _ending(int(status), str(stdout or ""), str(stderr or ""))
            for mutant_id, status, stdout, stderr in rows
        }


def _ending(execution_status: int, stdout: str, stderr: str) -> Ending:
    route = kill_route(execution_status, stdout, stderr)
    if route == "address":
        kind = _ADDRESS_KIND.search(stderr)
        return Ending(route, kind.group(1) if kind else "")
    if route != "check":
        return Ending(route, "")
    check = _LIBSTDCXX_CHECK.search(stderr)
    refused = (check.group(1) or check.group(2) or "") if check else ""
    return Ending(route, _CHECK_VALUES.sub("", " ".join(refused.split())))


def lane_routes(sqlite_path: Path) -> dict[str, str]:
    """Read each mutant's route from one lane's SQLite report."""
    return {mutant: ending.route for mutant, ending in lane_endings(sqlite_path).items()}


def merge_endings(lanes: list[dict[str, Ending]]) -> dict[str, int]:
    """Count the mutants by route across the lanes' endings, as ``merge_routes`` does."""
    return merge_routes([{m: ending.route for m, ending in lane.items()} for lane in lanes])


def merge_routes(lanes: list[dict[str, str]]) -> dict[str, int]:
    """Count the mutants by route across the lanes, attributed in the order of ``KILL_ROUTES``."""
    counts: dict[str, int] = dict.fromkeys(KILL_ROUTES, 0)
    ids = {mutant for lane in lanes for mutant in lane}
    for mutant in ids:
        routes = {lane[mutant] for lane in lanes if mutant in lane}
        counts[next(route for route in KILL_ROUTES if route in routes)] += 1
    return counts
