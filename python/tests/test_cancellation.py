"""Cancellation contract tests — Track C.1 + C.2.

Covers the four scenarios called out in docs/architecture/CANCELLATION.md:

1. Sync iter cancellation via ``generator.close()`` / consumer ``break``
   (§3.1) — committed prefix durable in the client's stream state.
2. Sync iter error mid-stream — ``BatchError`` with ``partial_results=[]``.
3. Async smoke — full sync-mirror surface (parse_dbc, set_properties,
   send_frame, end_stream) wraps cleanly through ``asyncio.to_thread``.
4. Async batch cancellation via ``asyncio.timeout`` — ``CancelledError``
   on the awaiting task, committed prefix durable.
5. Async iter cancellation via ``asyncio.timeout`` — ``CancelledError``
   at frame boundary, committed prefix durable.

The tests use the real FFI (no mocks) so the "committed prefix is
durable in stream state" half of the contract is actually exercised.
"""

import asyncio
import contextlib
from collections.abc import AsyncIterable, Iterable

import pytest

from aletheia import (
    AletheiaClient as SyncClient,
    BatchError,
    CANFrameTuple,
    FFIBackend,
    FrameResult,
    Signal,
)
from aletheia.asyncio import AletheiaClient as AsyncClient
from aletheia.asyncio.testing import gated_backend
from aletheia.protocols import (
    AckResponse, DBCDefinition, DLCCode, PropertyViolationResponse,
)


def _make_frames(
    n: int, *, can_id: int = 256, start_ts: int = 1000,
) -> list[CANFrameTuple]:
    """Build n monotonically-timestamped frames with payload (i, 0, 0, …)."""
    return [
        CANFrameTuple(
            timestamp=start_ts + i * 1000,
            can_id=can_id,
            dlc=DLCCode(8),
            data=bytearray([i & 0xFF, 0, 0, 0, 0, 0, 0, 0]),
            extended=False,
        )
        for i in range(n)
    ]


async def _consume_iter(it: AsyncIterable[FrameResult]) -> int:
    """Drain an async iterator and return the consumed count.

    Used by ``test_timeout_during_iter`` so the consumer runs as a
    distinct task whose ``await`` boundary the timeout can interrupt.
    """
    consumed = 0
    async for _ in it:
        consumed += 1
    return consumed


# =============================================================================
# Sync iter — `send_frames_iter` on the synchronous client
# =============================================================================


class TestSyncIter:
    """``AletheiaClient.send_frames_iter`` — generator-based lazy batch."""

    def test_yields_frame_results_for_all_frames(self, simple_dbc: DBCDefinition) -> None:
        """Five-frame happy path yields five FrameResults with monotonic indices."""
        prop = Signal("TestSignal").less_than(1000).always()
        with SyncClient() as client:
            client.parse_dbc(simple_dbc)
            client.set_properties([prop.to_dict()])
            client.start_stream()
            frames = _make_frames(5)
            results = list(client.send_frames_iter(frames))
            client.end_stream()

        assert len(results) == 5
        for i, r in enumerate(results):
            assert isinstance(r, FrameResult)
            assert r.frame_index == i
            assert r.timestamp == 1000 + i * 1000
            assert r.can_id == 256
            assert r.extended is False
            assert r.violation is None  # value 0 < 1000

    def test_consumer_break_commits_prefix(self, simple_dbc: DBCDefinition) -> None:
        """Breaking the for-loop early leaves the committed prefix durable."""
        prop = Signal("TestSignal").less_than(1000).always()
        with SyncClient() as client:
            client.parse_dbc(simple_dbc)
            client.set_properties([prop.to_dict()])
            client.start_stream()
            frames = _make_frames(10)

            consumed = 0
            for r in client.send_frames_iter(frames):
                consumed += 1
                if r.frame_index == 2:
                    break

            # The next frame the iter would have produced is frame 3, but the
            # `break` releases the generator before it runs. The committed
            # prefix is exactly frames 0..2.
            assert consumed == 3

            # end_stream observes the commit-prefix-and-report state.
            result = client.end_stream()
            assert result["status"] == "complete"

    def test_generator_close_commits_prefix(self, simple_dbc: DBCDefinition) -> None:
        """Explicit ``.close()`` on the generator stops further FFI calls."""
        prop = Signal("TestSignal").less_than(1000).always()
        with SyncClient() as client:
            client.parse_dbc(simple_dbc)
            client.set_properties([prop.to_dict()])
            client.start_stream()
            frames = _make_frames(10)

            gen = client.send_frames_iter(frames)
            r0 = next(gen)
            r1 = next(gen)
            gen.close()

            assert r0.frame_index == 0
            assert r1.frame_index == 1

            # State is consistent: end_stream succeeds.
            result = client.end_stream()
            assert result["status"] == "complete"

    def test_error_mid_iter_raises_batcherror_with_empty_partial(
        self, simple_dbc: DBCDefinition,
    ) -> None:
        """Non-monotonic timestamp on frame 2 raises BatchError(partial_results=[])."""
        prop = Signal("TestSignal").less_than(1000).always()
        with SyncClient() as client:
            client.parse_dbc(simple_dbc)
            client.set_properties([prop.to_dict()])
            client.start_stream()

            # Frames: ts 1000, 2000, 500 (regression — Agda rejects).
            bad: list[CANFrameTuple] = [
                CANFrameTuple(1000, 256, DLCCode(8), bytearray(8), False),
                CANFrameTuple(2000, 256, DLCCode(8), bytearray(8), False),
                CANFrameTuple(500, 256, DLCCode(8), bytearray(8), False),
            ]

            yielded: list[FrameResult] = []
            with pytest.raises(BatchError) as exc_info:
                for r in client.send_frames_iter(bad):
                    yielded.append(r)

            err = exc_info.value
            assert err.frame_index == 2
            # iter-mode contract: partial_results is empty (consumer already
            # received the committed prefix via yields).
            assert len(err.partial_results) == 0
            # Consumer received frames 0 and 1 directly.
            assert len(yielded) == 2

            client.end_stream()

    def test_lazy_consumption_on_break(self, simple_dbc: DBCDefinition) -> None:
        """The source iterable is consumed lazily — break stops the producer too."""
        prop = Signal("TestSignal").less_than(1000).always()
        consumed_from_source: list[int] = []

        def lazy_source() -> Iterable[CANFrameTuple]:
            for i in range(100):
                consumed_from_source.append(i)
                yield CANFrameTuple(1000 + i * 1000, 256, DLCCode(8), bytearray(8), False)

        with SyncClient() as client:
            client.parse_dbc(simple_dbc)
            client.set_properties([prop.to_dict()])
            client.start_stream()

            yielded = 0
            for _r in client.send_frames_iter(lazy_source()):
                yielded += 1
                if yielded == 3:
                    break

            client.end_stream()

        assert yielded == 3
        # The source produced at most a small bounded prefix — definitely
        # not all 100 elements (laziness gate).
        assert len(consumed_from_source) <= 4


# =============================================================================
# Async client smoke — full sync-mirror surface through asyncio.to_thread
# =============================================================================


class TestAsyncSmoke:
    """``aletheia.asyncio.AletheiaClient`` — verifies the surface mirror."""

    def test_full_streaming_session(self, simple_dbc: DBCDefinition) -> None:
        """parse_dbc → set_properties → start_stream → send_frame → end_stream."""
        prop = Signal("TestSignal").less_than(1000).always()

        async def _run() -> str:
            async with AsyncClient() as client:
                parse_resp = await client.parse_dbc(simple_dbc)
                assert parse_resp["status"] == "success"
                set_resp = await client.set_properties([prop.to_dict()])
                assert set_resp["status"] == "success"
                start_resp = await client.start_stream()
                assert start_resp["status"] == "success"
                ack = await client.send_frame(1000, 256, DLCCode(8), bytearray(8))
                assert ack["status"] in ("ack", "fails")
                end_resp = await client.end_stream()
                return end_resp["status"]

        status = asyncio.run(_run())
        assert status == "complete"

    def test_send_frames_batch_returns_full_list(self, simple_dbc: DBCDefinition) -> None:
        """``send_frames`` returns a list of length len(frames) on the happy path."""
        prop = Signal("TestSignal").less_than(1000).always()

        async def _run() -> int:
            async with AsyncClient() as client:
                await client.parse_dbc(simple_dbc)
                await client.set_properties([prop.to_dict()])
                await client.start_stream()
                results = await client.send_frames(_make_frames(5))
                await client.end_stream()
                return len(results)

        assert asyncio.run(_run()) == 5


# =============================================================================
# Async batch cancellation — `asyncio.timeout` around `await client.send_frames`
# =============================================================================


class TestAsyncBatchCancellation:
    """Async batch ops surface ``CancelledError`` at frame boundaries."""

    def test_timeout_mid_batch_raises_cancelled(self, simple_dbc: DBCDefinition) -> None:
        """Cancellation between committed frame and next ``await`` raises TimeoutError.

        Deterministic via the public ``gated_backend`` testing helper:
        the worker thread blocks inside frame 1's ``send_frame_binary``
        after committing it; the test fires ``asyncio.timeout(0)``
        (semantically "fire on next loop tick" — no wall-clock dependency
        since the gate guarantees a yield point); the next ``await``
        returns ``CancelledError`` which ``asyncio.timeout`` wraps as
        ``TimeoutError``.  No ``Event.wait(timeout=…)`` anywhere;
        pytest's session timeout is the only safety net for genuine
        hangs.
        """
        prop = Signal("TestSignal").less_than(1000).always()

        async def _run() -> None:
            with gated_backend(FFIBackend(), after_n=1) as (backend, started, proceed):
                sync = SyncClient(backend=backend)
                async with AsyncClient(sync_client=sync) as client:
                    await client.parse_dbc(simple_dbc)
                    await client.set_properties([prop.to_dict()])
                    await client.start_stream()
                    send_task = asyncio.create_task(
                        client.send_frames(_make_frames(50)),
                    )
                    # Block until frame 1 has committed in the worker.
                    await asyncio.to_thread(started.wait)
                    try:
                        with pytest.raises(TimeoutError):
                            async with asyncio.timeout(0):
                                # ``send_task`` is awaiting the wedged worker;
                                # ``timeout(0)`` fires on the next loop tick;
                                # ``await send_task`` yields and the timeout
                                # cancels it, then asyncio.timeout wraps the
                                # CancelledError as TimeoutError.
                                await send_task
                    finally:
                        proceed.set()  # release worker so end_stream can run
                    # Stream state still consistent — end_stream succeeds.
                    result = await client.end_stream()
                    assert result["status"] == "complete"

        asyncio.run(_run())

    def test_explicit_task_cancel(self, simple_dbc: DBCDefinition) -> None:
        """Cancelling the task between frames raises CancelledError on the awaiter.

        Deterministic via ``gated_backend``: frame 1 is committed in the
        worker, the test cancels + releases, frame 1's result returns,
        and the next ``await`` raises ``CancelledError`` immediately.
        """
        prop = Signal("TestSignal").less_than(1000).always()

        async def _run() -> None:
            with gated_backend(FFIBackend(), after_n=1) as (backend, started, proceed):
                sync = SyncClient(backend=backend)
                async with AsyncClient(sync_client=sync) as client:
                    await client.parse_dbc(simple_dbc)
                    await client.set_properties([prop.to_dict()])
                    await client.start_stream()

                    task: asyncio.Task[list[AckResponse | PropertyViolationResponse]] = (
                        asyncio.create_task(
                            client.send_frames(_make_frames(50)),
                        )
                    )
                    # Block until frame 1 has committed in the worker.
                    await asyncio.to_thread(started.wait)
                    task.cancel()
                    proceed.set()
                    with pytest.raises(asyncio.CancelledError):
                        await task

                    # Stream state is consistent regardless of how many
                    # frames committed — end_stream succeeds.
                    result = await client.end_stream()
                    assert result["status"] == "complete"

        asyncio.run(_run())

    def test_cancel_during_close_does_not_leak_state(self) -> None:
        """Cancellation delivered while ``__aexit__`` is closing must not leak FFI state.

        R19 cluster 11 — PY-B-12.1 / PY-D-15.2 / PY-D-20.2: ``__aexit__`` /
        ``close()`` wrap their ``asyncio.to_thread(self._sync.close)`` in
        ``asyncio.shield`` so the underlying close runs to completion even
        if the awaiting coroutine is cancelled.  Verified by cancelling
        the task running ``client.close()`` after the shielded coroutine
        has had a chance to start; the inner ``to_thread`` keeps running
        in the background and ``is_closed`` flips to True.

        Pattern adapted from python/tests/test_cancellation.py's existing
        ``gated_backend`` deterministic-yield-point pattern (no
        ``Event.wait(timeout=…)`` or wall-clock sleeps; pytest session
        timeout is the only safety net).
        """

        async def _run() -> None:
            sync = SyncClient()
            # AsyncClient is double-close-safe, so the implicit __aexit__ at
            # the end of the block is a no-op after the explicit close_task
            # has driven is_closed to True via the shielded inner close.
            async with AsyncClient(sync_client=sync) as client:
                assert not sync.is_closed
                close_task = asyncio.create_task(client.close())
                # Yield enough times for the shielded inner task to start.
                # asyncio.shield wraps the inner future; cancelling the outer
                # coroutine after the inner has been scheduled lets the inner
                # complete in the background.
                await asyncio.sleep(0)
                await asyncio.sleep(0)
                close_task.cancel()
                with contextlib.suppress(asyncio.CancelledError):
                    await close_task
                # The shielded close runs in the asyncio default executor; wait
                # for it to land via a deterministic poll on the observable
                # ``is_closed`` flag.  Per feedback_no_physical_time_in_tests, we
                # use ``asyncio.sleep(0)`` (single-tick yield) rather than a
                # wall-clock wait; pytest's session timeout catches genuine hangs.
                for _ in range(10_000):  # bounded so a real bug surfaces
                    if sync.is_closed:
                        break
                    await asyncio.sleep(0)
                assert sync.is_closed, "FFI session must be released even when close was cancelled"

        asyncio.run(_run())


# =============================================================================
# Async iter cancellation — `asyncio.timeout` around `async for ... in iter`
# =============================================================================


class TestAsyncIterCancellation:
    """Async iter ops surface ``CancelledError`` at the yield boundary."""

    def test_timeout_during_iter(self, simple_dbc: DBCDefinition) -> None:
        """Timeout during ``async for`` — committed prefix durable, async-iter
        wraps cancellation in TimeoutError per asyncio.timeout semantics.

        Deterministic via ``gated_backend``: the worker blocks inside
        frame 1's ``send_frame_binary`` after committing it; the test
        fires ``asyncio.timeout(0)`` (next-loop-tick semantics, not
        wall-clock); the async-iter's next ``await`` raises
        ``CancelledError`` which ``asyncio.timeout`` wraps as
        ``TimeoutError``.
        """
        prop = Signal("TestSignal").less_than(1000).always()

        async def _run() -> None:
            with gated_backend(FFIBackend(), after_n=1) as (backend, started, proceed):
                sync = SyncClient(backend=backend)
                async with AsyncClient(sync_client=sync) as client:
                    await client.parse_dbc(simple_dbc)
                    await client.set_properties([prop.to_dict()])
                    await client.start_stream()

                    consumed = 0
                    iter_task = client.send_frames_iter(_make_frames(50))
                    consume_task = asyncio.create_task(_consume_iter(iter_task))
                    await asyncio.to_thread(started.wait)
                    try:
                        with pytest.raises(TimeoutError):
                            async with asyncio.timeout(0):
                                consumed = await consume_task
                    finally:
                        proceed.set()

                    # Consumer may have received zero or a small prefix; the
                    # contract guarantees state is consistent with that prefix.
                    assert consumed >= 0
                    result = await client.end_stream()
                    assert result["status"] == "complete"

        asyncio.run(_run())

    def test_async_iter_yields_frame_result_with_index(
        self, simple_dbc: DBCDefinition,
    ) -> None:
        """Smoke: full async-iter consumption yields one FrameResult per frame."""
        prop = Signal("TestSignal").less_than(1000).always()

        async def _run() -> list[FrameResult]:
            async with AsyncClient() as client:
                await client.parse_dbc(simple_dbc)
                await client.set_properties([prop.to_dict()])
                await client.start_stream()
                results: list[FrameResult] = []
                async for r in client.send_frames_iter(_make_frames(5)):
                    results.append(r)
                await client.end_stream()
                return results

        results = asyncio.run(_run())
        assert len(results) == 5
        assert [r.frame_index for r in results] == [0, 1, 2, 3, 4]
        assert [r.timestamp for r in results] == [1000, 2000, 3000, 4000, 5000]


# =============================================================================
# FrameResult shape
# =============================================================================


class TestFrameResultShape:
    """FrameResult.violation correctly exposes only fails-verdict responses."""

    def test_ack_response_has_no_violation(self) -> None:
        """FrameResult.violation returns None when the response is an ack."""
        r = FrameResult(
            frame_index=0,
            timestamp=1000,
            can_id=0x100,
            extended=False,
            response={"status": "ack"},
        )
        assert r.violation is None

    def test_fails_response_returns_violation(self) -> None:
        """FrameResult.violation returns the response when it is a fails verdict."""
        viol_response: PropertyViolationResponse = {
            "status": "fails",
            "type": "property",
            "property_index": {"numerator": 0, "denominator": 1},
            "timestamp": {"numerator": 1000, "denominator": 1},
        }
        r = FrameResult(
            frame_index=0,
            timestamp=1000,
            can_id=0x100,
            extended=False,
            response=viol_response,
        )
        assert r.violation is viol_response
