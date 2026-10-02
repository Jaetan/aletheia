# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
"""Deterministic scaffolding for testing code that uses the async client.

:class:`TurnExecutor` stands in for :func:`asyncio.to_thread` as the async
client's ``run_in_thread``: each sync call waits one turn of the event loop,
then runs to completion on the loop's own thread.  A call whose awaiter is
cancelled before its turn never runs, as an executor drops a job cancelled in
its queue, and once its turn comes it runs to completion, as a job a worker
has started does.  Calls therefore run in the order the loop gives them, the
same on every run, and :meth:`TurnExecutor.cancel_at` puts a cancellation on
an exact call: no test needs a thread, a timer or a second task.  It lives in
the package proper, beside the client it serves, so consumers testing their
own async usage have it too.

Usage::

    import asyncio
    from aletheia import AletheiaClient
    from aletheia.asyncio import AletheiaClient as AsyncClient
    from aletheia.asyncio.testing import CallCount, TurnExecutor

    async def run() -> None:
        executor = TurnExecutor()
        sync = AletheiaClient()
        async with AsyncClient(sync_client=sync, run_in_thread=executor) as client:
            await client.parse_dbc(dbc)
            await client.set_properties(properties)
            await client.start_stream()
            task = asyncio.current_task()
            assert task is not None
            executor.cancel_at(task, after=CallCount(2))  # frames 0 and 1 run
            try:
                await client.send_frames(frames)
            except asyncio.CancelledError:
                task.uncancel()
            await client.end_stream()
"""

from __future__ import annotations

import asyncio
from typing import TYPE_CHECKING, NewType

if TYPE_CHECKING:
    from collections.abc import Callable

# How many calls a TurnExecutor has queued or run, or how many from now a
# cancellation lands at.
CallCount = NewType("CallCount", int)


class TurnExecutor:
    """Runs each sync call at its turn on the event loop, as a one-worker executor would.

    ``queued`` counts every call handed to it; ``ran`` counts the calls that
    ran to completion, so neither a call dropped by a cancellation before its
    turn nor one that raised is among them.
    """

    def __init__(self) -> None:
        """Start with no call queued, none run and no cancellation named."""
        self.queued = CallCount(0)
        self.ran = CallCount(0)
        self._cancel: Callable[[], bool] | None = None
        self._cancel_at = CallCount(0)

    def cancel_at[R](self, task: asyncio.Task[R], after: CallCount) -> None:
        """Cancel ``task`` as the call ``after`` calls from now is queued.

        ``after`` of 0 names the next call.  The cancellation is delivered at
        that call's turn, so the call is dropped when ``task`` is the one
        awaiting it, and still runs when another task awaits it, as a shielded
        call does.
        """
        self._cancel, self._cancel_at = task.cancel, CallCount(self.queued + after)

    async def __call__[**P, T](self, fn: Callable[P, T], /, *args: P.args, **kwargs: P.kwargs) -> T:
        """Queue ``fn(*args, **kwargs)``, wait one turn of the loop, then run it."""
        if self._cancel is not None and self.queued == self._cancel_at:
            _ = self._cancel()
            self._cancel = None
        self.queued = CallCount(self.queued + 1)
        await asyncio.sleep(0)  # the call's turn: a cancellation delivered here drops it
        result = fn(*args, **kwargs)
        self.ran = CallCount(self.ran + 1)
        return result


__all__ = ["CallCount", "TurnExecutor"]
