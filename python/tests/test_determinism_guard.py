# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
"""Tests for the runtime guard, ``tools/_determinism_guard.py``, run on planted tests.

The guard holds what a test reaches, the code under test included: no clock, no
wait on a duration, no thread, no process unless the test's mark says which
claim needs it, and no core count but the default asked of the runtime unless a
mark says why and the runtime is started.  Each plant is a test run in a session inside this one,
under the guard: what it does must fail it, or must not.  The plants are
strings, so the static gate reads them as the fixtures they are.
"""

from __future__ import annotations

import textwrap

import pytest

from tools import _determinism_guard
from tools._determinism_guard import AuditEvent, CoreCount, MarkName
from tools.check_test_determinism import SourceText


def _run_guarded(pytester: pytest.Pytester, test: SourceText) -> pytest.RunResult:
    """Run one test file under the guard, in a session inside this test's process."""
    _ = pytester.makeconftest('pytest_plugins = ["tools._determinism_guard"]')
    _ = pytester.makepyfile(test_plant=textwrap.dedent(test))
    return pytester.runpytest_inprocess("-p", "no:cacheprovider")


# What a refusal of a clock, a wait or a thread says, after the call it refuses.
_TIME_RULE = "a test reads no clock, waits on no duration and starts no thread"


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
    result.stdout.fnmatch_lines([f"*Failed: time.sleep(0): {_TIME_RULE}"])


def test_every_refusal_the_code_caught_is_reported(pytester: pytest.Pytester) -> None:
    """A test whose code caught two refusals fails at teardown naming both."""
    result = _run_guarded(
        pytester,
        SourceText(
            """\
            import time
            def test_plant():
                for secs in (0, 1):
                    try:
                        time.sleep(secs)
                    except BaseException:
                        pass
            """
        ),
    )
    result.assert_outcomes(passed=1, errors=1)
    result.stdout.fnmatch_lines(
        [f"*Failed: time.sleep(0): {_TIME_RULE}", f"*time.sleep(1): {_TIME_RULE}"]
    )


def _module_fixture_plant(body: SourceText) -> SourceText:
    """Plant a test whose module fixture, set up before its own fixtures, runs ``body``."""
    return SourceText(
        "import time\nimport pytest\n\n"
        + '@pytest.fixture(scope="module")\n'
        + f"def sleeper():\n    {body}\n\n"
        + "def test_plant(sleeper):\n    pass\n"
    )


def test_a_module_fixture_s_refusal_fails_its_test_s_setup(pytester: pytest.Pytester) -> None:
    """A module fixture's refusal fails the test it was set up for, not the session's runner."""
    result = _run_guarded(pytester, _module_fixture_plant(SourceText("time.sleep(0)")))
    result.assert_outcomes(errors=1)
    assert "time.sleep(0)" in result.stdout.str()


def test_a_module_fixture_s_caught_refusal_fails_its_test_s_teardown(
    pytester: pytest.Pytester,
) -> None:
    """A refusal a module fixture's code caught fails its test at teardown, as a test's own does."""
    caught = "try:\n        time.sleep(0)\n    except BaseException:\n        pass"
    result = _run_guarded(pytester, _module_fixture_plant(SourceText(caught)))
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


@pytest.mark.parametrize("name", [MarkName("process"), MarkName("runtime_cores")])
@pytest.mark.parametrize(
    "arguments",
    [SourceText(""), SourceText('("")'), SourceText('("  ")'), SourceText('(reason="the claim")')],
    ids=["bare", "empty", "blank", "keyword"],
)
def test_a_mark_without_one_reason_fails_at_setup(
    pytester: pytest.Pytester, name: MarkName, arguments: SourceText
) -> None:
    """A process or cores mark gives one reason that is not blank, positionally, or fails first."""
    plant = f"import pytest\n\n@pytest.mark.{name}{arguments}\ndef test_plant():\n    pass\n"
    result = _run_guarded(pytester, SourceText(plant))
    result.assert_outcomes(errors=1)
    result.stdout.fnmatch_lines([f'*@pytest.mark.{name} takes one reason, as "<reason>"'])


def test_a_mark_without_a_reason_fails_before_the_test_s_fixtures(
    pytester: pytest.Pytester,
) -> None:
    """The mark's own check runs first, so a fixture's refusal cannot hide it."""
    result = _run_guarded(
        pytester,
        SourceText(
            """\
            import time
            import pytest

            @pytest.fixture
            def sleeper():
                time.sleep(0)

            @pytest.mark.runtime_cores
            def test_plant(sleeper):
                pass
            """
        ),
    )
    result.assert_outcomes(errors=1)
    result.stdout.fnmatch_lines(['*@pytest.mark.runtime_cores takes one reason, as "<reason>"'])
    assert "time.sleep(0)" not in result.stdout.str()


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


# --- The runtime's cores.

# What a refusal of a core count says, after the request it refuses.
_CORES_RULE = (
    "a client starts the runtime on the default core count, and a test asks a started"
    + " runtime for another only where the answer is its claim, saying which with"
    + ' @pytest.mark.runtime_cores("<reason>")'
)


# A test asking ``count`` of a runtime a first client started, and of one not yet started.
_STARTED = """\
from aletheia import AletheiaClient

def test_plant():
    with AletheiaClient(), AletheiaClient(rts_cores={count}):
        pass
"""
_UNSTARTED = """\
from aletheia import RTSState

def test_plant(monkeypatch):
    monkeypatch.setattr(RTSState, "initialized", False)
    RTSState.acquire(None, {count})
"""


@pytest.mark.parametrize(
    ("plant", "count"),
    [
        pytest.param(SourceText(_STARTED), CoreCount(2), id="started"),
        pytest.param(SourceText(_UNSTARTED), CoreCount(2), id="unstarted"),
        # A count below the default is another count too.
        pytest.param(SourceText(_UNSTARTED), CoreCount(0), id="below"),
    ],
)
def test_the_guard_fails_a_test_that_asks_another_core_count_unmarked(
    pytester: pytest.Pytester, plant: SourceText, count: CoreCount
) -> None:
    """Another count fails an unmarked test, started runtime or not, before the runtime sees it."""
    result = _run_guarded(pytester, SourceText(plant.format(count=count)))
    result.assert_outcomes(failed=1)
    result.stdout.fnmatch_lines(
        [f"*test_plant.py::test_plant asked the runtime for {count} cores: {_CORES_RULE}"]
    )


def test_an_ask_without_a_count_asks_the_default(pytester: pytest.Pytester) -> None:
    """``RTSState.acquire`` called without a count asks the default, as the real one does."""
    result = _run_guarded(
        pytester,
        SourceText(
            """\
            from aletheia import AletheiaClient, RTSState

            def test_plant():
                with AletheiaClient():
                    RTSState.acquire(RTSState.lib)
                    RTSState.release()
            """
        ),
    )
    result.assert_outcomes(passed=1)


def test_a_module_fixture_s_ask_is_held_to_its_test(pytester: pytest.Pytester) -> None:
    """A module fixture asks in its first user's setup, so its test's mark decides the request."""
    result = _run_guarded(
        pytester,
        SourceText(
            """\
            import pytest
            from aletheia import RTSState

            @pytest.fixture(scope="module")
            def runtime():
                with pytest.MonkeyPatch.context() as patch:
                    patch.setattr(RTSState, "initialized", False)
                    RTSState.acquire(None, 2)

            def test_plant(runtime):
                pass
            """
        ),
    )
    result.assert_outcomes(errors=1)
    result.stdout.fnmatch_lines(
        [f"*test_plant.py::test_plant asked the runtime for 2 cores: {_CORES_RULE}"]
    )


def test_an_ask_at_import_fails_the_collection(pytester: pytest.Pytester) -> None:
    """A module that asks another count when imported asks it outside any test, and fails."""
    result = _run_guarded(
        pytester,
        SourceText(
            """\
            import pytest
            from aletheia import RTSState

            with pytest.MonkeyPatch.context() as patch:
                patch.setattr(RTSState, "initialized", False)
                RTSState.acquire(None, 2)

            def test_plant():
                pass
            """
        ),
    )
    result.assert_outcomes(errors=1)
    result.stdout.fnmatch_lines(
        [f"*the runtime was asked for 2 cores outside any test: {_CORES_RULE}"]
    )


def test_a_marked_test_asks_a_started_runtime_another_count(pytester: pytest.Pytester) -> None:
    """A test whose mark gives its reason asks a started runtime another count, and is warned."""
    result = _run_guarded(
        pytester,
        SourceText(
            """\
            import pytest
            from aletheia import AletheiaClient

            @pytest.mark.runtime_cores("the warning is the claim")
            def test_plant(caplog):
                with caplog.at_level("WARNING", logger="aletheia"), AletheiaClient():
                    with AletheiaClient(rts_cores=4):
                        pass
                assert "rts.cores_mismatch" in caplog.text
            """
        ),
    )
    result.assert_outcomes(passed=1)


def test_a_mark_never_lets_a_test_start_the_runtime_on_another_count(
    pytester: pytest.Pytester,
) -> None:
    """A marked test asks a started runtime only: the count a runtime starts on is the default."""
    result = _run_guarded(
        pytester,
        SourceText(
            """\
            import pytest
            from aletheia import RTSState

            @pytest.mark.runtime_cores("the warning is the claim")
            def test_plant(monkeypatch):
                monkeypatch.setattr(RTSState, "initialized", False)
                RTSState.acquire(None, 4)
            """
        ),
    )
    result.assert_outcomes(failed=1)
    result.stdout.fnmatch_lines(
        [f"*test_plant.py::test_plant would start the runtime on 4 cores: {_CORES_RULE}"]
    )


def test_a_cores_mark_on_a_test_that_asks_the_default_fails(pytester: pytest.Pytester) -> None:
    """A mark that allows a count its test never asks is standing permission, and fails."""
    result = _run_guarded(
        pytester,
        SourceText(
            """\
            import pytest
            from aletheia import AletheiaClient

            @pytest.mark.runtime_cores("the warning is the claim")
            def test_plant():
                with AletheiaClient():
                    pass
            """
        ),
    )
    result.assert_outcomes(failed=1)
    result.stdout.fnmatch_lines(
        ["*test_plant: its runtime_cores mark allows a core count it never asks"]
    )
