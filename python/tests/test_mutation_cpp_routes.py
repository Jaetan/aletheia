# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
"""Tests for ``tools.mutation_routes``, the kill-route census of the C++ lane.

Mull's SQLite report keeps, per mutant and per lane, the execution status,
the exit status and the test binary's own output. The census reads what
ended each run: a test's assertion, a leak the sanitizer reported, a read or
a write the address sanitizer reported, the kernel ending the process, a
check the standard library runs in the mutation build, or a fault, and
attributes a mutant several lanes killed to the first of those
routes, since a test's assertion is the one kill the suite gives without any
instrument. The rows the mutants attributed to a check or a fault become are
``test_mutation_unobserved_ledger``'s subject; here the reading is the route.
"""

from __future__ import annotations

import contextlib
import sqlite3
from typing import TYPE_CHECKING, NewType

import pytest

from tools.mutation_cpp import cpp_kill_routes
from tools.mutation_cpp_legs import CppLeg, CppTree, sliced_legs
from tools.mutation_routes import (
    KILL_ROUTES,
    MULL_PASSED,
    MULL_TIMEDOUT,
    Ending,
    MutantRun,
    kill_route,
    lane_endings,
    merge_routes,
)

from aletheia.common_types import ExitStatus

if TYPE_CHECKING:
    from collections.abc import Mapping
    from pathlib import Path

# The identifier Mull names a mutant by.
_Mutant = NewType("_Mutant", str)

_FAILED = 1
# The exit statuses the lanes' runs end with, as Mull records them: 0 where
# the tests passed, Catch2's after a failed assertion, -1 where a signal ended
# the process and left none, LeakSanitizer's where it ended the run, and the
# kernel's where its error path did.
_PASSED = ExitStatus(0)
_TEST_FAILED = ExitStatus(42)
_BY_SIGNAL = ExitStatus(-1)
_LEAK_SANITIZER = ExitStatus(23)
_KERNEL_ENDED = ExitStatus(1)
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
    ("run", "route"),
    [
        (MutantRun(MULL_PASSED, _PASSED, _SUMMARY_PASSED, ""), "survived"),
        (MutantRun(MULL_TIMEDOUT, _BY_SIGNAL, "", ""), "timeout"),
        (MutantRun(_FAILED, _TEST_FAILED, _ASSERTION + _RULE + _SUMMARY_FAILED, ""), "test"),
        (MutantRun(_FAILED, _KERNEL_ENDED, _ASSERTION, "aletheia: x\n"), "test"),
        (MutantRun(_FAILED, _BY_SIGNAL, _FATAL + _SUMMARY_FAILED, _LIBSTDCXX_ASSERTION), "check"),
        (MutantRun(_FAILED, _BY_SIGNAL, _FATAL + _SUMMARY_FAILED, _DEBUG_MODE), "check"),
        (
            MutantRun(
                _FAILED, _BY_SIGNAL, _ASSERTION + _RULE + _FATAL + _SUMMARY_FAILED, _DEBUG_MODE
            ),
            "test",
        ),
        (MutantRun(_FAILED, _BY_SIGNAL, _ASSERTION + _RULE + _FATAL + _SUMMARY_FAILED, ""), "test"),
        (MutantRun(_FAILED, _BY_SIGNAL, _FATAL + _RULE + _ASSERTION + _SUMMARY_FAILED, ""), "test"),
        (
            MutantRun(
                _FAILED, _LEAK_SANITIZER, "", "==1==ERROR: LeakSanitizer: detected memory leaks\n"
            ),
            "leak",
        ),
        (
            MutantRun(
                _FAILED, _KERNEL_ENDED, "", "aletheia: aletheia_process: Return code (4) not ok\n"
            ),
            "kernel",
        ),
        (MutantRun(_FAILED, _LEAK_SANITIZER, _FATAL + _SUMMARY_FAILED, _SIGNAL), "fault"),
        (MutantRun(_FAILED, _LEAK_SANITIZER, "", _SIGNAL), "fault"),
        (MutantRun(_FAILED, _BY_SIGNAL, "", ""), "fault"),
    ],
)
def test_a_run_is_read_by_what_ended_it(run: MutantRun, route: str) -> None:
    """The status is read first, then the exit status, the test output and the error output.

    A failure Catch2 reports for a fatal signal is not an assertion, so a run
    whose only failed blocks name a fatal condition died by whatever the error
    output says: the library's check where it printed one, a fault otherwise.
    One assertion anywhere in the output makes the kill the test's, whichever
    came first, and whatever ended the process after it.
    """
    assert kill_route(run) == route


def test_a_failed_test_mull_kept_no_output_for_is_read_by_its_exit(tmp_path: Path) -> None:
    """Catch2's failure exit is the test's kill where the report kept no output.

    Mull keeps nothing of a stream holding a byte that is not UTF-8, so a
    failure report quoting raw input reaches the report empty. A signal ends
    the process with no exit status, so the same empty output there is a fault.
    """
    _write_lane(
        tmp_path / "lane.sqlite",
        {
            _Mutant("failed"): MutantRun(_FAILED, _TEST_FAILED, "", ""),
            _Mutant("signalled"): MutantRun(_FAILED, _BY_SIGNAL, "", ""),
        },
    )
    assert lane_endings(tmp_path / "lane.sqlite") == {
        "failed": Ending("test", ""),
        "signalled": Ending("fault", ""),
    }


def test_a_mutant_several_lanes_killed_takes_the_first_route() -> None:
    """An assertion in any lane attributes the mutant to the test, whatever the other lanes read."""
    lanes = [
        {"a": "fault", "b": "leak", "c": "survived", "d": "timeout", "e": "fault", "f": "address"},
        {"a": "test", "b": "fault", "c": "survived", "d": "fault", "e": "check", "f": "fault"},
    ]
    assert merge_routes(lanes) == {
        "test": 1,
        "leak": 1,
        "address": 1,
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
        {
            _Mutant("debug"): MutantRun(_FAILED, _BY_SIGNAL, _FATAL, _DEBUG_MODE),
            _Mutant("wrapped"): MutantRun(_FAILED, _BY_SIGNAL, _FATAL, _DEBUG_MODE_WRAPPED),
            _Mutant("assertion"): MutantRun(_FAILED, _BY_SIGNAL, _FATAL, _LIBSTDCXX_ASSERTION),
            _Mutant("signal"): MutantRun(_FAILED, _LEAK_SANITIZER, _FATAL, _SIGNAL),
            _Mutant("test"): MutantRun(
                _FAILED, _BY_SIGNAL, _ASSERTION + _SUMMARY_FAILED, _DEBUG_MODE
            ),
        },
    )
    assert lane_endings(tmp_path / "lane.sqlite") == {
        "debug": Ending("check", "attempt to dereference a past-the-end iterator."),
        "wrapped": Ending("check", "attempt to subscript container with out-of-bounds index"),
        "assertion": Ending("check", "__offset <= size()"),
        "signal": Ending("fault", ""),
        "test": Ending("test", ""),
    }


def _write_lane(path: Path, runs: Mapping[_Mutant, MutantRun]) -> None:
    # closing() closes the connection; sqlite3's own context manager only
    # commits, which would leave the file open until a collection.
    with contextlib.closing(sqlite3.connect(path)) as conn:
        _ = conn.execute(
            "CREATE TABLE mutant (mutant_id TEXT, execution_status INT, exit_status INT,"
            + " stdout TEXT, stderr TEXT)"
        )
        _ = conn.executemany(
            "INSERT INTO mutant VALUES (?, ?, ?, ?, ?)",
            [(mutant, *run) for mutant, run in runs.items()],
        )
        conn.commit()


def test_the_census_reads_every_leg_report(tmp_path: Path) -> None:
    """The counts come from the legs' SQLite reports, named as the legs name them.

    A mutant is in one slice per tree, so it is read by one leg of each tree,
    and a route it took in any of them is the route it is attributed by.
    """
    legs = sliced_legs()
    for leg in legs:
        # Two mutants per slice, named for the slice, so no two legs of a tree
        # carry one identifier: that is what the partition guarantees.
        killed, survived = _Mutant(f"k{leg}"), _Mutant(f"s{leg}")
        stdout = _ASSERTION + _SUMMARY_FAILED if leg.tree is CppTree.PLAIN else ""
        _write_lane(
            tmp_path / f"{leg.report_name}.sqlite",
            {
                killed: MutantRun(_FAILED, _TEST_FAILED, stdout, ""),
                survived: MutantRun(MULL_PASSED, _PASSED, _SUMMARY_PASSED, ""),
            },
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
    _write_lane(
        tmp_path / f"{legs[0].report_name}.sqlite",
        {_Mutant("m1"): MutantRun(_FAILED, _TEST_FAILED, "", "")},
    )
    assert cpp_kill_routes(tmp_path, legs) is None


def test_a_whole_tree_sweep_is_read_by_its_own_legs(tmp_path: Path) -> None:
    """An unsliced run names its reports by tree alone, and the census reads those."""
    legs = [CppLeg(tree) for tree in CppTree]
    for leg in legs:
        _write_lane(
            tmp_path / f"{leg.report_name}.sqlite",
            {_Mutant("m1"): MutantRun(_FAILED, _TEST_FAILED, _ASSERTION + _SUMMARY_FAILED, "")},
        )
    routes = cpp_kill_routes(tmp_path, legs)
    assert routes is not None
    assert routes["test"] == 1
