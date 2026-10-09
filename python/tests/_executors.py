# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
"""An executor that runs every call on the test's own thread, in an order the test picks.

The tools run their concurrent calls on what an ``executor`` factory builds, a
thread pool by default; a test hands them this one instead, since a test starts
no thread (AGENTS.md, Universal Rules).  A submitted call waits until a result
is asked for or the executor shuts down; then the waiting calls run one at a
time, first submitted first or last submitted first.  The last-first order
finishes calls in the reverse of their submission, which a test needs to tell
an order kept by submission from an order kept by completion.
"""

from __future__ import annotations

from concurrent.futures import Executor, Future
from enum import Enum
from typing import TYPE_CHECKING, Self, SupportsFloat, override

if TYPE_CHECKING:
    from collections.abc import Callable
    from types import TracebackType

    from tools._common import WorkerCount


class Order(Enum):
    """Which waiting call runs next."""

    FIRST_SUBMITTED = "first submitted"
    LAST_SUBMITTED = "last submitted"


class _Settles[T]:
    """Settle a future with the exception its call raised, which then goes on."""

    def __init__(self, future: Future[T]) -> None:
        self._future = future

    def __enter__(self) -> Self:
        return self

    def __exit__(
        self,
        kind: type[BaseException] | None,
        raised: BaseException | None,
        traceback: TracebackType | None,
    ) -> None:
        if raised is not None:
            self._future.set_exception(raised)


class DrivenExecutor(Executor):
    """Run each submitted call on the calling thread, when its result is asked for."""

    def __init__(self, _workers: WorkerCount, order: Order = Order.FIRST_SUBMITTED) -> None:
        """Take the worker count a factory is called with, which one thread ignores."""
        self._order = order
        self._waiting: list[Callable[[], None]] = []

    @override
    def submit[**P, T](self, fn: Callable[P, T], /, *args: P.args, **kwargs: P.kwargs) -> Future[T]:
        future = _DrivenFuture[T](self)

        def turn() -> None:
            if future.set_running_or_notify_cancel():
                with _Settles(future):
                    future.set_result(fn(*args, **kwargs))

        self._waiting.append(turn)
        return future

    def run_next(self) -> None:
        """Run the next waiting call; an exception it raised goes on to the caller."""
        index = 0 if self._order is Order.FIRST_SUBMITTED else -1
        self._waiting.pop(index)()

    @override
    def shutdown(self, wait: bool = True, *, cancel_futures: bool = False) -> None:
        """Run every call still waiting, whatever ``wait`` and ``cancel_futures`` ask."""
        while self._waiting:
            self.run_next()


class _DrivenFuture[T](Future[T]):
    """A future whose result, when asked for, runs the waiting calls until it is settled."""

    def __init__(self, executor: DrivenExecutor) -> None:
        super().__init__()
        self._executor = executor

    def settle(self) -> None:
        """Run waiting calls until this one is settled."""
        while not self.done():
            self._executor.run_next()

    @override
    def result(self, timeout: SupportsFloat | None = None) -> T:
        """Settle this future, then return its result, which a settled future has at once."""
        self.settle()
        return super().result(None if timeout is None else float(timeout))
