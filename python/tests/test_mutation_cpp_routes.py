# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
"""Tests for ``tools.mutation_routes``, the kill-route census of the C++ lane.

Mull's SQLite report keeps, per mutant and per lane, the execution status
and the test binary's own output. The census reads what ended each run: a
test's assertion, a leak the sanitizer reported, the kernel ending the
process, a check the standard library runs in the mutation build, or a
fault, and attributes a mutant several lanes killed to the first of those
routes, since a test's assertion is the one kill the suite gives without any
instrument. The rows the mutants attributed to a check or a fault become are
``test_mutation_unobserved_ledger``'s subject; here the reading is the route.
"""

from __future__ import annotations

import sqlite3
from typing import TYPE_CHECKING

import pytest

from tools.mutation_cpp import CppLeg, CppTree, cpp_kill_routes, sliced_legs
from tools.mutation_routes import (
    KILL_ROUTES,
    MULL_PASSED,
    MULL_TIMEDOUT,
    Ending,
    kill_route,
    lane_endings,
    merge_routes,
)

if TYPE_CHECKING:
    from pathlib import Path

_FAILED = 1
_RULE = "-" * 79 + "\n"
_SUMMARY_FAILED = "=" * 79 + "\ntest cases:  562 |  557 passed | 5 failed\n"
_SUMMARY_PASSED = "All tests passed (6008 assertions in 562 test cases)\n"
_ASSERTION = (
    "/tree/cpp/tests/unit_tests_log.cpp:74: FAILED:\n  REQUIRE( count(name) == 1 )\n"
    "with expansion:\n  0 == 1\n\n"
)
_FATAL = (
    "/tree/cpp/tests/excel_tests.cpp:187: FAILED:\n  {Unknown expression after the reported line}\n"
    "due to a fatal error condition:\n  SIGABRT - Abort (abnormal termination) signal\n\n"
)
# What libstdc++ prints before it aborts: the lightweight assertion's one line,
# and debug mode's report of the operation it refused.
_LIBSTDCXX_ASSERTION = (
    "/usr/include/c++/16/span:436: subspan(size_type, size_type) const "
    "[_Type = const std::byte, _Extent = 18446744073709551615]: "
    "Assertion '__offset <= size()' failed.\n"
)
_DEBUG_MODE = (
    "/usr/include/c++/16/debug/safe_iterator.h:372:\nIn function:\n"
    "    pointer gnu_debug::_Safe_iterator<...>::operator->() const\n\n"
    "Error: attempt to dereference a past-the-end iterator.\n\n"
    'Objects involved in the operation:\n    iterator "this" @ 0x1 {\n'
)
# The subscript check wraps what it refused over two lines.
_DEBUG_MODE_WRAPPED = (
    "/usr/include/c++/16/debug/vector:512:\nIn function:\n"
    "    reference std::__debug::vector<int>::operator[](size_type)\n\n"
    "Error: attempt to subscript container with out-of-bounds index 42, but \n"
    "container only holds 8 elements.\n\n"
    "Objects involved in the operation:\n"
)
_SIGNAL = "LeakSanitizer:DEADLYSIGNAL\n==1==ERROR: LeakSanitizer: SEGV on unknown address 0x0\n"


@pytest.mark.parametrize(
    ("status", "stdout", "stderr", "route"),
    [
        (MULL_PASSED, _SUMMARY_PASSED, "", "survived"),
        (MULL_TIMEDOUT, "", "", "timeout"),
        (_FAILED, _ASSERTION + _RULE + _SUMMARY_FAILED, "", "test"),
        (_FAILED, _ASSERTION, "aletheia: x\n", "test"),
        (_FAILED, _FATAL + _SUMMARY_FAILED, _LIBSTDCXX_ASSERTION, "check"),
        (_FAILED, _FATAL + _SUMMARY_FAILED, _DEBUG_MODE, "check"),
        (_FAILED, _ASSERTION + _RULE + _FATAL + _SUMMARY_FAILED, _DEBUG_MODE, "test"),
        (_FAILED, _ASSERTION + _RULE + _FATAL + _SUMMARY_FAILED, "", "test"),
        (_FAILED, _FATAL + _RULE + _ASSERTION + _SUMMARY_FAILED, "", "test"),
        (_FAILED, "", "==1==ERROR: LeakSanitizer: detected memory leaks\n", "leak"),
        (_FAILED, "", "aletheia: aletheia_process: Return code (4) not ok\n", "kernel"),
        (_FAILED, _FATAL + _SUMMARY_FAILED, _SIGNAL, "fault"),
        (_FAILED, "", _SIGNAL, "fault"),
        (_FAILED, "", "", "fault"),
    ],
)
def test_a_run_is_read_by_what_ended_it(status: int, stdout: str, stderr: str, route: str) -> None:
    """The status is read first, then the test output, then the error output.

    A failure Catch2 reports for a fatal signal is not an assertion, so a run
    whose only failed blocks name a fatal condition died by whatever the error
    output says: the library's check where it printed one, a fault otherwise.
    One assertion anywhere in the output makes the kill the test's, whichever
    came first, and whatever ended the process after it.
    """
    assert kill_route(status, stdout, stderr) == route


def test_a_mutant_several_lanes_killed_takes_the_first_route() -> None:
    """An assertion in any lane attributes the mutant to the test, whatever the other lanes read."""
    lanes = [
        {"a": "fault", "b": "leak", "c": "survived", "d": "timeout", "e": "fault"},
        {"a": "test", "b": "fault", "c": "survived", "d": "fault", "e": "check"},
    ]
    assert merge_routes(lanes) == {
        "test": 1,
        "leak": 1,
        "kernel": 0,
        "check": 1,
        "fault": 1,
        "timeout": 0,
        "survived": 1,
    }
    assert tuple(merge_routes(lanes)) == KILL_ROUTES


def test_an_ending_carries_what_the_check_refused(tmp_path: Path) -> None:
    """The invariant after ``Error:`` or inside the assertion's quotes, without the values.

    Debug mode prints the index and the size it refused them for; those come
    from the test data, so the ledger keyed on this text would move with a
    fixture rather than with a claim.
    """
    _write_lane(
        tmp_path / "lane.sqlite",
        [
            ("debug", _FAILED, _FATAL, _DEBUG_MODE),
            ("wrapped", _FAILED, _FATAL, _DEBUG_MODE_WRAPPED),
            ("assertion", _FAILED, _FATAL, _LIBSTDCXX_ASSERTION),
            ("signal", _FAILED, _FATAL, _SIGNAL),
            ("test", _FAILED, _ASSERTION + _SUMMARY_FAILED, _DEBUG_MODE),
        ],
    )
    assert lane_endings(tmp_path / "lane.sqlite") == {
        "debug": Ending("check", "attempt to dereference a past-the-end iterator."),
        "wrapped": Ending("check", "attempt to subscript container with out-of-bounds index"),
        "assertion": Ending("check", "__offset <= size()"),
        "signal": Ending("fault", ""),
        "test": Ending("test", ""),
    }


def _write_lane(path: Path, rows: list[tuple[str, int, str, str]]) -> None:
    with sqlite3.connect(path) as conn:
        _ = conn.execute(
            "CREATE TABLE mutant (mutant_id TEXT, execution_status INT, stdout TEXT, stderr TEXT)"
        )
        _ = conn.executemany("INSERT INTO mutant VALUES (?, ?, ?, ?)", rows)


def test_the_census_reads_every_leg_report(tmp_path: Path) -> None:
    """The counts come from the legs' SQLite reports, named as the legs name them.

    A mutant is in one slice per tree, so it is read by two of the six legs,
    and a route it took in either is the route it is attributed by.
    """
    legs = sliced_legs()
    for leg in legs:
        # Two mutants per slice, named for the slice, so no two legs of a tree
        # carry one identifier: that is what the partition guarantees.
        killed, survived = f"k{leg}", f"s{leg}"
        stdout = _ASSERTION + _SUMMARY_FAILED if leg.tree is CppTree.PLAIN else ""
        _write_lane(
            tmp_path / f"{leg.report_name}.sqlite",
            [(killed, _FAILED, stdout, ""), (survived, MULL_PASSED, _SUMMARY_PASSED, "")],
        )
    routes = cpp_kill_routes(tmp_path, legs)
    assert routes is not None
    # Each tree's three slices carry two mutants each, and the trees carry
    # different identifiers here, so the census is every leg's rows.
    assert sum(routes.values()) == 2 * len(legs)
    assert routes["survived"] == len(legs)


def test_a_leg_without_a_report_leaves_no_census(tmp_path: Path) -> None:
    """Part of a census would misattribute every mutant the missing leg killed."""
    legs = sliced_legs()
    _write_lane(tmp_path / f"{legs[0].report_name}.sqlite", [("m1", _FAILED, "", "")])
    assert cpp_kill_routes(tmp_path, legs) is None


def test_a_whole_tree_sweep_is_read_by_its_own_legs(tmp_path: Path) -> None:
    """An unsliced run names its reports by tree alone, and the census reads those."""
    legs = [CppLeg(tree) for tree in CppTree]
    for leg in legs:
        _write_lane(
            tmp_path / f"{leg.report_name}.sqlite",
            [("m1", _FAILED, _ASSERTION + _SUMMARY_FAILED, "")],
        )
    routes = cpp_kill_routes(tmp_path, legs)
    assert routes is not None
    assert routes["test"] == 1
