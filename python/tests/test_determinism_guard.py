# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
"""Tests for the runtime guard, ``tools/_determinism_guard.py``, run on planted tests.

The guard holds what a test reaches, the code under test included: no clock, no
wait on a duration, no thread, and no process unless the test's mark says
which claim needs it.  Each plant is a test run in a session inside this one,
under the guard: what it does must fail it, or must not.  The plants are
strings, so the static gate reads them as the fixtures they are.
"""

from __future__ import annotations

import textwrap

import pytest

from tools import _determinism_guard
from tools._determinism_guard import AuditEvent
from tools.check_test_determinism import SourceText


def _run_guarded(pytester: pytest.Pytester, test: SourceText) -> pytest.RunResult:
    """Run one test file under the guard, in a session inside this test's process."""
    _ = pytester.makeconftest('pytest_plugins = ["tools._determinism_guard"]')
    _ = pytester.makepyfile(test_plant=textwrap.dedent(test))
    return pytester.runpytest_inprocess("-p", "no:cacheprovider")


@pytest.mark.parametrize(
    ("call", "refusal"),
    [
        ("import threading; threading.Thread(target=print).start()", "a thread started"),
        ("import _thread; _thread.start_new_thread(print, ())", "a thread started on print"),
        ("import _thread; _thread.start_joinable_thread(print)", "a thread started on print"),
        ("import time; time.sleep(0)", "time.sleep(0)"),
        ("import threading; threading.Event().wait(0.01)", "a wait of 0.01 s on a condition"),
        ("import threading; threading.Event().wait(0)", "a wait of 0 s on a condition"),
        ("import queue; queue.Queue().get(timeout=0.01)", "s on a condition"),
        (
            "import subprocess; subprocess.Popen.__new__(subprocess.Popen).wait(timeout=1)",
            "a process waited on for 1 s",
        ),
        (
            "import subprocess; subprocess.Popen.__new__(subprocess.Popen).wait(timeout=0)",
            "a process waited on for 0 s",
        ),
        (
            "import subprocess; subprocess.Popen.__new__(subprocess.Popen).communicate(timeout=1)",
            "a process waited on for 1 s",
        ),
        ("import select; select.select([], [], [], 0)", "a select of 0 s"),
        ("import signal; signal.alarm(1)", "an alarm set 1 s ahead"),
        ("import signal; signal.setitimer(signal.ITIMER_REAL, 1)", "a timer set 1 s ahead"),
        ("import asyncio; asyncio.run(asyncio.sleep(1))", "a callback scheduled 1.0 s ahead"),
    ],
)
def test_the_guard_fails_a_test_that_waits_or_starts_a_thread(
    pytester: pytest.Pytester, call: SourceText, refusal: SourceText
) -> None:
    """A thread, a sleep, a timed wait or a timer fails the test that reaches it, named."""
    result = _run_guarded(pytester, SourceText(f"def test_plant():\n    {call}\n"))
    result.assert_outcomes(failed=1)
    assert refusal in result.stdout.str()


@pytest.mark.parametrize(
    "call",
    [
        "import asyncio; asyncio.run(asyncio.sleep(0))",
        "import signal; signal.alarm(0)",
        "import signal; signal.setitimer(signal.ITIMER_REAL, 0)",
        "import threading; e = threading.Event(); e.set(); e.wait()",
        "import asyncio; loop = asyncio.new_event_loop(); loop.call_later(0, print); loop.close()",
    ],
)
def test_the_guard_lets_a_test_yield_cancel_a_timer_or_wait_on_what_is_done(
    pytester: pytest.Pytester, call: SourceText
) -> None:
    """A zero sleep on a loop yields, a zero timer cancels one, and a set event waits on nothing."""
    result = _run_guarded(pytester, SourceText(f"def test_plant():\n    {call}\n"))
    result.assert_outcomes(passed=1)


def test_the_guard_fails_a_test_whose_code_caught_the_refusal(pytester: pytest.Pytester) -> None:
    """A refusal the code under test swallowed still fails the test, at its teardown."""
    result = _run_guarded(
        pytester,
        SourceText(
            """\
            import time
            def test_plant():
                try:
                    time.sleep(0)
                except BaseException:
                    pass
            """
        ),
    )
    result.assert_outcomes(passed=1, errors=1)
    assert "time.sleep(0)" in result.stdout.str()


def test_every_test_reads_one_clock_that_moves_only_when_told(pytester: pytest.Pytester) -> None:
    """The clocks and calendars all read the guard's clock, from the same instant in every test."""
    result = _run_guarded(
        pytester,
        SourceText(
            """\
            import datetime, time
            import pytest
            from tools._determinism_guard import Seconds

            START = 1_767_225_600

            def test_the_clocks_agree_and_stand_still():
                assert time.time() == time.monotonic() == time.perf_counter() == START
                assert time.time_ns() == time.monotonic_ns() == START * 1_000_000_000
                assert time.perf_counter_ns() == time.process_time_ns() == START * 1_000_000_000
                assert time.thread_time_ns() == START * 1_000_000_000
                assert time.gmtime()[:6] == (2026, 1, 1, 0, 0, 0)
                assert datetime.datetime.now(datetime.UTC) == datetime.datetime(
                    2026, 1, 1, tzinfo=datetime.UTC
                )
                assert datetime.date.today() == datetime.date.fromtimestamp(START)
                assert isinstance(datetime.datetime.now(), datetime.datetime)
                assert datetime.datetime.today() == datetime.datetime.fromtimestamp(START)
                assert datetime.datetime.utcnow() == datetime.datetime(2026, 1, 1)
                assert time.process_time() == time.thread_time() == START
                assert time.clock_gettime(time.CLOCK_MONOTONIC) == START
                assert time.clock_gettime_ns(time.CLOCK_MONOTONIC) == START * 1_000_000_000
                assert time.localtime() == time.localtime(START)
                assert time.ctime() == time.ctime(START)
                assert time.asctime() == time.asctime(time.localtime(START))
                assert time.strftime("%Y-%m-%d") == time.strftime("%Y-%m-%d", time.localtime(START))
                assert time.gmtime(0)[:6] == (1970, 1, 1, 0, 0, 0)
                assert time.mktime(time.localtime(0)) == 0
                assert time.ctime(0) == time.asctime(time.localtime(0))
                assert time.strftime("%Y", time.gmtime(0)) == "1970"
                assert time.time() == START

            def test_the_clock_moves_by_what_the_test_advances(clock):
                clock.advance(Seconds(2.5))
                assert time.monotonic() == START + 2.5

            def test_the_clock_never_moves_back(clock):
                with pytest.raises(ValueError, match="moves forward"):
                    clock.advance(Seconds(-1))
                assert time.time() == START

            def test_the_next_test_starts_from_the_same_instant():
                assert time.time() == START
            """
        ),
    )
    result.assert_outcomes(passed=4)


def test_a_session_inside_a_test_leaves_the_guard_on(pytester: pytest.Pytester) -> None:
    """The guard stays until the last session that installed it ends, not the first."""
    _run_guarded(pytester, SourceText("def test_plant():\n    pass\n")).assert_outcomes(passed=1)
    assert _determinism_guard.installed()


# --- Processes.

# What a refusal of a process start says, after its test's id and event.
_PROCESS_RULE = "a test starts a process only where its claim is that process's own answer*"


# Each way to start a process, and the event its refusal names: the first one
# it raises, so a subprocess call is refused before it opens a pipe.
_STARTS = [
    (
        SourceText("import subprocess, sys; subprocess.run([sys.executable, '-c', 'pass'])"),
        AuditEvent("subprocess.Popen"),
    ),
    (SourceText("import os; os.system('true')"), AuditEvent("os.system")),
    (SourceText("import os; os.fork()"), AuditEvent("os.fork")),
    (
        SourceText("import os, sys; os.posix_spawn(sys.executable, [sys.executable], {})"),
        AuditEvent("os.posix_spawn"),
    ),
    (SourceText("import os; os.forkpty()"), AuditEvent("os.forkpty")),
    # An exec the guard let through would end this run, so it ends it failing.
    (SourceText("import os; os.execv('/bin/sh', ['sh', '-c', 'exit 3'])"), AuditEvent("os.exec")),
    (
        SourceText(
            "import multiprocessing.util as u, sys;"
            + " u.spawnv_passfds(sys.executable.encode(), [sys.executable, '-c', 'pass'], ())"
        ),
        AuditEvent("_posixsubprocess.fork_exec"),
    ),
]


@pytest.mark.parametrize(("start", "event"), _STARTS)
def test_the_guard_fails_a_test_that_starts_a_process_unmarked(
    pytester: pytest.Pytester, start: SourceText, event: AuditEvent
) -> None:
    """A process start in a test without a process mark fails it, before the process starts."""
    result = _run_guarded(pytester, SourceText(f"def test_plant():\n    {start}\n"))
    result.assert_outcomes(failed=1)
    result.stdout.fnmatch_lines(
        [f"*test_plant.py::test_plant started a process ({event}): {_PROCESS_RULE}"]
    )


def test_a_marked_test_starts_the_process_its_claim_needs(pytester: pytest.Pytester) -> None:
    """A test whose mark gives its reason starts its process, and the process answers."""
    result = _run_guarded(
        pytester,
        SourceText(
            """
            import subprocess, sys
            import pytest

            @pytest.mark.process("the child's exit status is the claim")
            def test_plant():
                assert subprocess.run([sys.executable, "-c", "raise SystemExit(3)"]).returncode == 3
            """
        ),
    )
    result.assert_outcomes(passed=1)


@pytest.mark.parametrize(
    "mark",
    [
        SourceText("@pytest.mark.process"),
        SourceText('@pytest.mark.process("")'),
        SourceText('@pytest.mark.process("  ")'),
        SourceText('@pytest.mark.process(reason="the claim")'),
    ],
)
def test_a_process_mark_without_one_reason_fails_at_setup(
    pytester: pytest.Pytester, mark: SourceText
) -> None:
    """A process mark gives one non-empty reason, positionally, or its test fails before it runs."""
    result = _run_guarded(
        pytester, SourceText(f"import pytest\n\n{mark}\ndef test_plant():\n    pass\n")
    )
    result.assert_outcomes(errors=1)
    result.stdout.fnmatch_lines(["*@pytest.mark.process takes one reason*"])


def test_a_mark_on_a_test_that_starts_no_process_fails(pytester: pytest.Pytester) -> None:
    """A mark that allows a process its test never starts is standing permission, and fails."""
    result = _run_guarded(
        pytester,
        SourceText(
            """
            import pytest

            @pytest.mark.process("the child's exit status is the claim")
            def test_plant():
                pass
            """
        ),
    )
    result.assert_outcomes(failed=1)
    result.stdout.fnmatch_lines(["*its process mark allows a process it never starts*"])


def test_a_shared_fixture_s_process_covers_the_tests_that_rely_on_it(
    pytester: pytest.Pytester,
) -> None:
    """A module fixture starts its process once; its later users rely on it, and pass.

    A fixture of the same name in another module, which starts nothing, covers
    nothing: its marked user fails.
    """
    _ = pytester.makeconftest('pytest_plugins = ["tools._determinism_guard"]')
    _ = pytester.makepyfile(
        test_starts=textwrap.dedent(
            """
            import subprocess, sys
            import pytest

            @pytest.fixture(scope="module")
            def child():
                command = [sys.executable, "-c", "print(7)"]
                return subprocess.run(command, capture_output=True, text=True).stdout

            @pytest.mark.process("the child's output is the claim")
            def test_first(child):
                assert child == "7\\n"

            @pytest.mark.process("the child's output is the claim")
            def test_second(child):
                assert child == "7\\n"
            """
        ),
        test_starts_nothing=textwrap.dedent(
            """
            import pytest

            @pytest.fixture(scope="module")
            def child():
                return "7\\n"

            @pytest.mark.process("the child's output is the claim")
            def test_third(child):
                assert child == "7\\n"
            """
        ),
    )
    result = pytester.runpytest_inprocess("-p", "no:cacheprovider")
    result.assert_outcomes(passed=2, failed=1)
    result.stdout.fnmatch_lines(["*test_starts_nothing.py::test_third: its process mark allows*"])


def test_a_process_started_at_import_fails_the_collection(pytester: pytest.Pytester) -> None:
    """A module that starts a process when imported starts it outside any test, and fails."""
    result = _run_guarded(
        pytester,
        SourceText(
            """
            import subprocess, sys

            ROOT = subprocess.run([sys.executable, "-c", "pass"])

            def test_plant():
                pass
            """
        ),
    )
    result.assert_outcomes(errors=1)
    result.stdout.fnmatch_lines([f"*a process started outside any test (*): {_PROCESS_RULE}"])
