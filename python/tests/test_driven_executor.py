# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
"""The tests' executor runs each call on the test's own thread, in the order the test picks."""

from __future__ import annotations

from typing import NewType

import pytest
from _executors import DrivenExecutor, Order

from tools._common import WorkerCount

# The name of a call, recorded when it runs.
Call = NewType("Call", str)


def _fail(name: Call) -> None:
    """Raise the error a failing call raises."""
    msg = f"{name} failed"
    raise ValueError(msg)


def test_a_call_waits_until_a_result_is_asked_for_and_calls_run_first_submitted_first() -> None:
    """Nothing runs at submission; asking for the second result runs the first, then the second."""
    ran: list[Call] = []
    executor = DrivenExecutor(WorkerCount(2))
    _ = executor.submit(ran.append, Call("a"))
    second = executor.submit(ran.append, Call("b"))
    assert not ran
    second.result()
    assert ran == [Call("a"), Call("b")]


def test_the_last_submitted_call_runs_first_in_that_order() -> None:
    """Asking for the first result under the last-first order runs the later call before it."""
    ran: list[Call] = []
    executor = DrivenExecutor(WorkerCount(2), order=Order.LAST_SUBMITTED)
    first = executor.submit(ran.append, Call("a"))
    _ = executor.submit(ran.append, Call("b"))
    first.result()
    assert ran == [Call("b"), Call("a")]


def test_a_call_s_error_goes_on_to_the_caller_and_stays_in_its_own_future() -> None:
    """An error a call raises leaves the result that ran it, and its own future keeps it."""
    ran: list[Call] = []
    executor = DrivenExecutor(WorkerCount(2), order=Order.LAST_SUBMITTED)
    first = executor.submit(ran.append, Call("a"))
    failing = executor.submit(_fail, Call("b"))
    with pytest.raises(ValueError, match="b failed"):
        first.result()
    assert isinstance(failing.exception(), ValueError)
    first.result()
    assert ran == [Call("a")]


def test_shutting_down_runs_every_call_still_waiting() -> None:
    """Leaving the executor's block runs what no result asked for."""
    ran: list[Call] = []
    with DrivenExecutor(WorkerCount(1)) as executor:
        _ = executor.submit(ran.append, Call("a"))
        _ = executor.submit(ran.append, Call("b"))
        assert not ran
    assert ran == [Call("a"), Call("b")]


def test_a_cancelled_call_never_runs() -> None:
    """A call cancelled before its turn is passed over."""
    ran: list[Call] = []
    executor = DrivenExecutor(WorkerCount(1))
    assert executor.submit(ran.append, Call("a")).cancel()
    executor.shutdown()
    assert not ran
