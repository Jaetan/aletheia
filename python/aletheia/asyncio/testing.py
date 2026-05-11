"""Deterministic test scaffolding for async cancellation contracts.

Public testing helpers used by ``python/tests/test_cancellation.py`` and
available to downstream consumers writing async-cancel regression tests
for their own AletheiaClient usage.  Lives in the package proper (not
under ``tests/``) because:

1. Cross-binding parity — Go has the same need for a cancellation test
   primitive (covered by its native ``context.WithCancel`` pattern); C++
   has ``std::stop_token`` directly.  Python's equivalent must be
   discoverable at the same level.
2. The gate uses a public dependency-injection seam
   (``AletheiaClient(sync_client=...)``) and a public synchronization
   primitive (``threading.Event``) — no protected access, no mock
   patching, no test-specific suppressions required.

Usage::

    from aletheia import AletheiaClient
    from aletheia.asyncio import AletheiaClient as AsyncClient
    from aletheia.asyncio.testing import gate_send_frame

    sync = AletheiaClient()
    with gate_send_frame(sync, after_n=1) as (started, proceed):
        async with AsyncClient(sync_client=sync) as client:
            await client.parse_dbc(dbc)
            ...
            task = asyncio.create_task(client.send_frames(frames))
            await asyncio.to_thread(started.wait)  # frame 1 committed
            task.cancel()
            proceed.set()  # release the worker
            with pytest.raises(asyncio.CancelledError):
                await task
"""

from __future__ import annotations

import threading
from collections.abc import Generator
from contextlib import contextmanager

from ..client import AletheiaClient as _SyncClient
from ..protocols import DLCCode


@contextmanager
def gate_send_frame(
    sync_client: _SyncClient, after_n: int,
) -> Generator[tuple[threading.Event, threading.Event], None, None]:
    """Wrap ``sync_client.send_frame`` so call number ``after_n`` blocks.

    Yields ``(started, proceed)``.  The worker signals ``started`` once
    the n-th call has committed and waits on ``proceed`` before
    returning.  The caller runs cancel/timeout logic and sets
    ``proceed`` to release the worker.  This pins the cancellation
    point deterministically between frame ``after_n - 1`` (committed)
    and frame ``after_n`` (the next ``await`` raises
    ``CancelledError``), eliminating any dependence on physical-time
    races (no ``Event.wait(timeout=…)`` anywhere — pytest's session
    timeout is the only safety net for genuine hangs, which by design
    indicate a real bug rather than a flaky test).

    The wrap is restored on context exit (also fires on test exception);
    ``proceed.set()`` runs in the ``finally`` so a failing test cannot
    leak the worker thread.

    Decorates the public ``send_frame`` method on the public
    :class:`aletheia.AletheiaClient`; no private-attribute access, no
    monkey-patching of an underscore-prefixed member.  This is the
    cross-binding-equivalent of Go's ``context.WithCancel`` test
    pattern and C++'s ``std::stop_token`` rendezvous in
    ``cpp/tests/unit_tests_cancel.cpp``.
    """
    started = threading.Event()
    proceed = threading.Event()
    original = sync_client.send_frame
    counter = [0]

    # The argument list mirrors AletheiaClient.send_frame's public signature
    # exactly (4 positional + 1 keyword-only) so the wrap is transparent to
    # callers and `original(...)` re-dispatches without surprise.  The arity
    # is structural — the method has 5 parameters and the gate must too.
    def gated(
        timestamp: int, can_id: int, dlc: DLCCode, data: bytes | bytearray,
        *, extended: bool = False,
    ) -> object:
        counter[0] += 1
        result = original(timestamp, can_id, dlc, data, extended=extended)
        if counter[0] == after_n:
            started.set()
            proceed.wait()
        return result

    # Monkey-patch via setattr: pyright correctly flags direct
    # `sync_client.send_frame = gated` because methods are class-level
    # read-only members, but setattr is dynamic and acceptable for the
    # documented test-only rebind pattern.  Restored in `finally` so
    # exceptions in the body don't leak the wrap.
    setattr(sync_client, "send_frame", gated)
    try:
        yield started, proceed
    finally:
        setattr(sync_client, "send_frame", original)
        proceed.set()
