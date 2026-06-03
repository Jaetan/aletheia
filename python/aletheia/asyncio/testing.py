# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
"""Deterministic test scaffolding for async cancellation contracts.

Public testing helpers used by ``python/tests/test_cancellation.py`` and
available to downstream consumers writing async-cancel regression tests
for their own AletheiaClient usage.  Lives in the package proper (not
under ``tests/``) because:

1. Cross-binding parity — Go has the same need for a cancellation test
   primitive (covered by its native ``context.WithCancel`` pattern); C++
   has ``std::stop_token`` directly.  Python's equivalent must be
   discoverable at the same level.
2. The gate wraps a public :class:`aletheia.Backend` implementation
   (the DI seam) and is injected through
   :class:`aletheia.AletheiaClient.__init__`'s ``backend=`` kwarg.  No
   ``setattr`` monkey-patching, no protected-attribute access, no
   bound-method swap — instead, routes through the public Backend DI seam.

Usage::

    from aletheia import AletheiaClient, FFIBackend
    from aletheia.asyncio import AletheiaClient as AsyncClient
    from aletheia.asyncio.testing import gated_backend

    with gated_backend(FFIBackend(), after_n=1) as (backend, started, proceed):
        sync = AletheiaClient(backend=backend)
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
from contextlib import contextmanager
from typing import TYPE_CHECKING

if TYPE_CHECKING:
    from collections.abc import Generator

    from aletheia.client import Backend


class _CountingGateBackend:
    """Delegating :class:`Backend` that blocks send_frame_binary call N.

    Every method delegates to ``inner`` unchanged except
    :meth:`send_frame_binary`, which counts invocations.  When the
    counter reaches ``after_n``, the wrapper sets ``started`` and waits
    on ``proceed`` before invoking the inner backend.  Releasing
    ``proceed`` lets the worker complete that call and any subsequent
    ones; the counter does not reset.

    The wrapper carries no ``Backend(Protocol)`` inheritance assertion
    at class level — structural typing covers it — but is structurally
    interchangeable with any :class:`Backend` implementation.
    """

    def __init__(
        self,
        inner: Backend,
        *,
        after_n: int,
        started: threading.Event,
        proceed: threading.Event,
    ) -> None:
        self._inner = inner
        self._after_n = after_n
        self._started = started
        self._proceed = proceed
        self._counter = 0

    @property
    def call_count(self) -> int:
        """Number of times :meth:`send_frame_binary` has been invoked."""
        return self._counter

    # --- gated method --------------------------------------------------

    def send_frame_binary(  # noqa: PLR0913  # pylint: disable=too-many-arguments
        self,
        state: int,
        *,
        timestamp: int,
        can_id: int,
        extended: bool,
        dlc: int,
        data: bytes | bytearray,
        brs: bool | None,
        esi: bool | None,
    ) -> bytes:
        """Count this call, block if it's the ``after_n``-th, then delegate."""
        self._counter += 1
        if self._counter == self._after_n:
            self._started.set()
            self._proceed.wait()
        # R0801 false positive: forwarding the full ``send_frame_binary`` wire
        # signature necessarily mirrors the sync streaming path; a shared helper
        # would couple this test backend to the hot path it deliberately wraps.
        # pylint: disable=duplicate-code
        return self._inner.send_frame_binary(
            state,
            timestamp=timestamp,
            can_id=can_id,
            extended=extended,
            dlc=dlc,
            data=data,
            brs=brs,
            esi=esi,
        )
        # pylint: enable=duplicate-code

    # --- pure delegation ----------------------------------------------

    def init(self) -> int:
        """Delegate to the inner backend."""
        return self._inner.init()

    def close(self, state: int) -> None:
        """Delegate to the inner backend."""
        self._inner.close(state)

    def process(self, state: int, input_bytes: bytes) -> bytes:
        """Delegate to the inner backend."""
        return self._inner.process(state, input_bytes)

    def send_error_binary(self, state: int, timestamp: int) -> bytes:
        """Delegate to the inner backend."""
        return self._inner.send_error_binary(state, timestamp)

    def send_remote_binary(
        self,
        state: int,
        *,
        timestamp: int,
        can_id: int,
        extended: bool,
    ) -> bytes:
        """Delegate to the inner backend."""
        return self._inner.send_remote_binary(
            state,
            timestamp=timestamp,
            can_id=can_id,
            extended=extended,
        )

    def start_stream_binary(self, state: int) -> bytes:
        """Delegate to the inner backend."""
        return self._inner.start_stream_binary(state)

    def end_stream_binary(self, state: int) -> bytes:
        """Delegate to the inner backend."""
        return self._inner.end_stream_binary(state)

    def format_dbc_binary(self, state: int) -> bytes:
        """Delegate to the inner backend."""
        return self._inner.format_dbc_binary(state)

    def extract_signals_binary(  # pylint: disable=too-many-arguments
        self,
        state: int,
        *,
        can_id: int,
        extended: bool,
        dlc: int,
        data: bytes | bytearray,
    ) -> bytes:
        """Delegate to the inner backend."""
        return self._inner.extract_signals_binary(
            state,
            can_id=can_id,
            extended=extended,
            dlc=dlc,
            data=data,
        )

    def build_frame_bin(  # noqa: PLR0913  # pylint: disable=too-many-arguments
        self,
        state: int,
        *,
        can_id: int,
        extended: bool,
        dlc: int,
        indices: tuple[int, ...],
        numerators: tuple[int, ...],
        denominators: tuple[int, ...],
        expected_bytes: int,
    ) -> bytes:
        """Delegate to the inner backend."""
        return self._inner.build_frame_bin(
            state,
            can_id=can_id,
            extended=extended,
            dlc=dlc,
            indices=indices,
            numerators=numerators,
            denominators=denominators,
            expected_bytes=expected_bytes,
        )

    def update_frame_bin(  # noqa: PLR0913  # pylint: disable=too-many-arguments
        self,
        state: int,
        *,
        can_id: int,
        extended: bool,
        dlc: int,
        data: bytes | bytearray,
        indices: tuple[int, ...],
        numerators: tuple[int, ...],
        denominators: tuple[int, ...],
        expected_bytes: int,
    ) -> bytes:
        """Delegate to the inner backend."""
        return self._inner.update_frame_bin(
            state,
            can_id=can_id,
            extended=extended,
            dlc=dlc,
            data=data,
            indices=indices,
            numerators=numerators,
            denominators=denominators,
            expected_bytes=expected_bytes,
        )

    def extract_signals_bin(  # pylint: disable=too-many-arguments
        self,
        state: int,
        *,
        can_id: int,
        extended: bool,
        dlc: int,
        data: bytes | bytearray,
    ) -> bytes:
        """Delegate to the inner backend."""
        return self._inner.extract_signals_bin(
            state,
            can_id=can_id,
            extended=extended,
            dlc=dlc,
            data=data,
        )


@contextmanager
def gated_backend(
    inner: Backend,
    after_n: int,
) -> Generator[tuple[Backend, threading.Event, threading.Event]]:
    """Yield a Backend that blocks the *n*-th ``send_frame_binary`` call.

    Yields ``(backend, started, proceed)``.  The worker signals
    ``started`` once call number ``after_n`` has been observed and waits
    on ``proceed`` before returning to the inner backend.  The caller
    runs cancel/timeout logic and sets ``proceed`` to release the worker.
    This pins the cancellation point deterministically between frame
    ``after_n - 1`` (committed) and frame ``after_n`` (the next
    ``await`` raises ``CancelledError``), eliminating any dependence on
    physical-time races (no ``Event.wait(timeout=…)`` anywhere —
    pytest's session timeout is the only safety net for genuine hangs,
    which by design indicate a real bug rather than a flaky test).

    ``proceed.set()`` runs in ``finally`` so a failing test cannot leak
    the worker thread.

    Cross-binding parity:

    * Go: ``context.WithCancel`` + ``select { case <- ctx.Done() }``
      directly cancels in-flight; mocks gate via ``MockBackend``'s
      response queue + an external sync.Cond.
    * C++: ``std::stop_token`` rendezvous in
      ``cpp/tests/unit_tests_cancel.cpp``.
    * Python (this): wrap the Backend, count calls, ``threading.Event``
      rendezvous — closes the polymorphic gap left open by Python's
      cooperative-only cancellation model (``asyncio.CancelledError``
      fires at the next ``await``).
    """
    started = threading.Event()
    proceed = threading.Event()
    backend = _CountingGateBackend(
        inner,
        after_n=after_n,
        started=started,
        proceed=proceed,
    )
    try:
        yield backend, started, proceed
    finally:
        proceed.set()


__all__ = ["gated_backend"]
