# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
"""Tests for ``tools.mutation_routes``, the kill-route census of the C++ lane.

Mull's SQLite report keeps, per mutant and per leg, the execution status,
the exit status and the test binary's own output. The census reads what
ended each run: a test's assertion, the kernel ending the process, a check
the standard library runs in the mutation build, or a fault, and counts the
mutants by route over the legs, which are disjoint. The rows the mutants
attributed to a check or a fault become are ``test_mutation_unobserved_ledger``'s
subject; here the reading is the route.
"""

from __future__ import annotations

import contextlib
import sqlite3
from typing import TYPE_CHECKING, NewType

import pytest

from tools.mutation_cpp import cpp_endings
from tools.mutation_cpp_legs import CppLeg, sliced_legs
from tools.mutation_routes import (
    KILL_ROUTES,
    MULL_PASSED,
    MULL_TIMEDOUT,
    Ending,
    MutantRun,
    kill_route,
    lane_endings,
    merge_endings,
    merge_routes,
)

from aletheia.common_types import ExitStatus

if TYPE_CHECKING:
    from collections.abc import Mapping
    from pathlib import Path

# The identifier Mull names a mutant by.
_Mutant = NewType("_Mutant", str)

_FAILED = 1
# The exit statuses the legs' runs end with, as Mull records them: 0 where
# the tests passed, Catch2's after a failed assertion, -1 where a signal ended
# the process and left none, a sanitizer runtime's where one ended the run,
# and the kernel's where its error path did.
_PASSED = ExitStatus(0)
_TEST_FAILED = ExitStatus(42)
_BY_SIGNAL = ExitStatus(-1)
_SANITIZER_RUNTIME = ExitStatus(23)
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
# The tree carries no sanitizer, so its report is read as what it is: an end
# no test and no check named.
_LEAK_REPORT = "==1==ERROR: LeakSanitizer: detected memory leaks\n"


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
        (MutantRun(_FAILED, _SANITIZER_RUNTIME, "", _LEAK_REPORT), "fault"),
        (
            MutantRun(
                _FAILED, _KERNEL_ENDED, "", "aletheia: aletheia_process: Return code (4) not ok\n"
            ),
            "kernel",
        ),
        (MutantRun(_FAILED, _SANITIZER_RUNTIME, _FATAL + _SUMMARY_FAILED, _SIGNAL), "fault"),
        (MutantRun(_FAILED, _SANITIZER_RUNTIME, "", _SIGNAL), "fault"),
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


def test_the_routes_are_counted_over_the_legs() -> None:
    """Each leg's mutants are counted by route, every route counted, in the order ranking kills."""
    legs = [
        {"a": "fault", "b": "kernel", "c": "survived"},
        {"d": "timeout", "e": "check", "f": "test", "g": "survived"},
    ]
    assert merge_routes(legs) == {
        "test": 1,
        "kernel": 1,
        "check": 1,
        "fault": 1,
        "timeout": 1,
        "survived": 2,
    }
    assert tuple(merge_routes(legs)) == KILL_ROUTES
    # A mutant two legs ended differently takes the first of its routes in this
    # order, so a test's own assertion outranks the kernel's refusal, which
    # outranks a library check, which outranks a bare fault; what ran out of
    # time or survived comes after every kill.
    assert KILL_ROUTES == ("test", "kernel", "check", "fault", "timeout", "survived")


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
            _Mutant("signal"): MutantRun(_FAILED, _SANITIZER_RUNTIME, _FATAL, _SIGNAL),
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

    A mutant is in one slice, so it is read by one leg, and the route it took
    there is the route it is attributed by.
    """
    legs = sliced_legs()
    for leg in legs:
        # Two mutants per slice, named for the slice, so no two legs carry one
        # identifier: that is what the partition guarantees.
        killed, survived = _Mutant(f"k{leg}"), _Mutant(f"s{leg}")
        stdout = _ASSERTION + _SUMMARY_FAILED
        _write_lane(
            tmp_path / f"{leg.report_name}.sqlite",
            {
                killed: MutantRun(_FAILED, _TEST_FAILED, stdout, ""),
                survived: MutantRun(MULL_PASSED, _PASSED, _SUMMARY_PASSED, ""),
            },
        )
    endings = cpp_endings(tmp_path, legs)
    assert endings is not None
    routes = merge_endings(endings)
    # The slices carry two mutants each, so the census is every leg's rows.
    assert sum(routes.values()) == 2 * len(legs)
    assert routes == {**dict.fromkeys(KILL_ROUTES, 0), "test": len(legs), "survived": len(legs)}


def test_a_leg_without_a_report_leaves_no_census(tmp_path: Path) -> None:
    """Part of a census would misattribute every mutant the missing leg killed."""
    legs = sliced_legs()
    _write_lane(
        tmp_path / f"{legs[0].report_name}.sqlite",
        {_Mutant("m1"): MutantRun(_FAILED, _TEST_FAILED, "", "")},
    )
    assert cpp_endings(tmp_path, legs) is None


def test_a_whole_tree_sweep_is_read_by_its_own_report(tmp_path: Path) -> None:
    """An unsliced run names its report without a slice, and the census reads that."""
    legs = [CppLeg()]
    _write_lane(
        tmp_path / f"{legs[0].report_name}.sqlite",
        {_Mutant("m1"): MutantRun(_FAILED, _TEST_FAILED, _ASSERTION + _SUMMARY_FAILED, "")},
    )
    endings = cpp_endings(tmp_path, legs)
    assert endings is not None
    routes = merge_endings(endings)
    assert routes["test"] == 1
