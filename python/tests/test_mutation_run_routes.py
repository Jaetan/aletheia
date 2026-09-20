# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
"""Tests for ``tools.mutation_routes``, the kill-route census of the C++ lane.

Mull's SQLite report keeps, per mutant and per lane, the execution status
and the test binary's own output. The census reads what ended each run: a
test's assertion, a leak the sanitizer reported, the kernel ending the
process, or a fault, and attributes a mutant several lanes killed to the
first of those routes, since a test's assertion is the one kill the suite
gives without any instrument.
"""

from __future__ import annotations

import sqlite3
from typing import TYPE_CHECKING

import pytest

from tools.mutation_routes import KILL_ROUTES, MULL_PASSED, MULL_TIMEDOUT, kill_route, merge_routes
from tools.mutation_run import CPP_LANES, cpp_kill_routes

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


@pytest.mark.parametrize(
    ("status", "stdout", "stderr", "route"),
    [
        (MULL_PASSED, _SUMMARY_PASSED, "", "survived"),
        (MULL_TIMEDOUT, "", "", "timeout"),
        (_FAILED, _ASSERTION + _RULE + _SUMMARY_FAILED, "", "test"),
        (_FAILED, _ASSERTION, "aletheia: x\n", "test"),
        (_FAILED, _FATAL + _SUMMARY_FAILED, "/usr/include/c++/16/span:436: Assertion.\n", "fault"),
        (_FAILED, _ASSERTION + _RULE + _FATAL + _SUMMARY_FAILED, "", "test"),
        (_FAILED, _FATAL + _RULE + _ASSERTION + _SUMMARY_FAILED, "", "test"),
        (_FAILED, "", "==1==ERROR: LeakSanitizer: detected memory leaks\n", "leak"),
        (_FAILED, "", "aletheia: aletheia_process: Return code (4) not ok\n", "kernel"),
        (_FAILED, "", "LeakSanitizer:DEADLYSIGNAL\n==1==ERROR: LeakSanitizer: SEGV\n", "fault"),
        (_FAILED, "", "/usr/include/c++/16/span:436: subspan: Assertion failed.\n", "fault"),
        (_FAILED, "", "", "fault"),
    ],
)
def test_a_run_is_read_by_what_ended_it(status: int, stdout: str, stderr: str, route: str) -> None:
    """The status is read first, then the test output, then the error output.

    A failure Catch2 reports for a fatal signal is not an assertion, so a run
    whose only failed blocks name a fatal condition died by a fault; one
    assertion anywhere in the output makes the kill the test's, whichever
    came first.
    """
    assert kill_route(status, stdout, stderr) == route


def test_a_mutant_several_lanes_killed_takes_the_first_route() -> None:
    """An assertion in any lane attributes the mutant to the test, whatever the other lanes read."""
    lanes = [
        {"a": "fault", "b": "leak", "c": "survived", "d": "timeout"},
        {"a": "test", "b": "fault", "c": "survived", "d": "fault"},
    ]
    assert merge_routes(lanes) == {
        "test": 1,
        "leak": 1,
        "kernel": 0,
        "fault": 1,
        "timeout": 0,
        "survived": 1,
    }
    assert tuple(merge_routes(lanes)) == KILL_ROUTES


def _write_lane(path: Path, rows: list[tuple[str, int, str, str]]) -> None:
    with sqlite3.connect(path) as conn:
        _ = conn.execute(
            "CREATE TABLE mutant (mutant_id TEXT, execution_status INT, stdout TEXT, stderr TEXT)"
        )
        _ = conn.executemany("INSERT INTO mutant VALUES (?, ?, ?, ?)", rows)


def test_the_census_reads_every_lane_report(tmp_path: Path) -> None:
    """The counts come from the lanes' SQLite reports, named as the lanes name them."""
    names = [f"cpp-mull-{sanitizer or 'plain'}.sqlite" for sanitizer, _ in CPP_LANES]
    _write_lane(
        tmp_path / names[0],
        [("m1", _FAILED, "", ""), ("m2", MULL_PASSED, _SUMMARY_PASSED, "")],
    )
    _write_lane(
        tmp_path / names[1],
        [
            ("m1", _FAILED, _ASSERTION + _SUMMARY_FAILED, ""),
            ("m2", MULL_PASSED, _SUMMARY_PASSED, ""),
        ],
    )
    routes = cpp_kill_routes(tmp_path)
    assert routes is not None
    assert routes["test"] == 1
    assert routes["survived"] == 1
    assert sum(routes.values()) == 2


def test_a_lane_without_a_report_leaves_no_census(tmp_path: Path) -> None:
    """Half a census would misattribute every mutant the missing lane killed."""
    _write_lane(tmp_path / "cpp-mull-leak.sqlite", [("m1", _FAILED, "", "")])
    assert cpp_kill_routes(tmp_path) is None
