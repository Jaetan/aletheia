# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
"""Cancellation contract tests.

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
durable in stream state" half of the contract is actually exercised.  The
async cancellation cases hand the client ``TurnExecutor`` as its
``run_in_thread``, which runs each call on the event loop in a fixed order and
cancels at an exact call, so no case starts a thread or a second task and every
run takes one path.
"""

import asyncio
from typing import TYPE_CHECKING, NewType

import pytest

from aletheia import (
    AletheiaClient as SyncClient,
)
from aletheia import (
    BatchError,
    CANFrameTuple,
    FrameResult,
    Signal,
)
from aletheia.asyncio import AletheiaClient as AsyncClient
from aletheia.asyncio.testing import CallCount, TurnExecutor
from aletheia.types import (
    DBCDefinition,
    DLCCode,
    PropertyBatchResponse,
    PropertyResultEntry,
)

if TYPE_CHECKING:
    from collections.abc import AsyncIterable, Awaitable, Iterable


def _main_task() -> asyncio.Task[None]:
    """Name the task the test body runs in, which ``asyncio.run`` made."""
    task = asyncio.current_task()
    assert task is not None
    return task


def _make_frames(
    n: int,
    *,
    can_id: int = 256,
    start_ts: int = 1000,
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
    """Drain an async iterator and return the consumed count."""
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
        self,
        simple_dbc: DBCDefinition,
    ) -> None:
        """Non-monotonic timestamp on frame 2 raises BatchError(partial_results=[])."""
        prop = Signal("TestSignal").less_than(1000).always()
        with SyncClient() as client:
            client.parse_dbc(simple_dbc)
            client.set_properties([prop.to_dict()])
            client.start_stream()

            # Frames: ts 1000, 2000, 500 (regression — Agda rejects).
            bad: list[CANFrameTuple] = [
                CANFrameTuple(1000, 256, DLCCode(8), bytearray(8), extended=False),
                CANFrameTuple(2000, 256, DLCCode(8), bytearray(8), extended=False),
                CANFrameTuple(500, 256, DLCCode(8), bytearray(8), extended=False),
            ]

            yielded: list[FrameResult] = []
            with pytest.raises(BatchError) as exc_info:
                yielded.extend(client.send_frames_iter(bad))

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
                yield CANFrameTuple(1000 + i * 1000, 256, DLCCode(8), bytearray(8), extended=False)

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
            async with AsyncClient(
                sync_client=SyncClient(), run_in_thread=TurnExecutor()
            ) as client:
                parse_resp = await client.parse_dbc(simple_dbc)
                assert parse_resp["status"] == "success"
                set_resp = await client.set_properties([prop.to_dict()])
                assert set_resp["status"] == "success"
                start_resp = await client.start_stream()
                assert start_resp["status"] == "success"
                ack = await client.send_frame(1000, 256, DLCCode(8), bytearray(8))
                # Non-violating frame acks; a violation returns a property_batch.
                if "type" in ack:
                    assert ack["type"] == "property_batch"
                else:
                    assert ack["status"] == "ack"
                end_resp = await client.end_stream()
                return end_resp["status"]

        status = asyncio.run(_run())
        assert status == "complete"

    def test_send_frames_batch_returns_full_list(self, simple_dbc: DBCDefinition) -> None:
        """``send_frames`` returns a list of length len(frames) on the happy path."""
        prop = Signal("TestSignal").less_than(1000).always()

        async def _run() -> int:
            async with AsyncClient(
                sync_client=SyncClient(), run_in_thread=TurnExecutor()
            ) as client:
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
        """A timeout around ``send_frames`` raises TimeoutError and leaves the stream usable.

        ``asyncio.timeout(0)`` fires on the next turn of the loop, which is the
        first frame's turn, so that frame is dropped before it runs, as a queued
        executor job is, and ``asyncio.timeout`` turns the cancellation into
        ``TimeoutError``.  The stream is then still consistent: no frame of the
        batch committed, and ``end_stream`` completes.
        """
        prop = Signal("TestSignal").less_than(1000).always()
        executor = TurnExecutor()

        async def _run() -> None:
            async with AsyncClient(sync_client=SyncClient(), run_in_thread=executor) as client:
                await client.parse_dbc(simple_dbc)
                await client.set_properties([prop.to_dict()])
                await client.start_stream()
                before = executor.ran
                with pytest.raises(TimeoutError):
                    async with asyncio.timeout(0):
                        _ = await client.send_frames(_make_frames(50))
                assert executor.ran == before, "a frame ran after the timeout fired"
                result = await client.end_stream()
                assert result["status"] == "complete"

        asyncio.run(_run())

    def test_explicit_task_cancel(self, simple_dbc: DBCDefinition) -> None:
        """Cancelling the task between frames raises CancelledError; the prefix stays committed.

        The cancel lands as the third frame is queued, so the first two run and
        the third is dropped; ``end_stream`` then completes over the committed
        prefix.
        """
        prop = Signal("TestSignal").less_than(1000).always()
        executor = TurnExecutor()

        async def _run() -> None:
            async with AsyncClient(sync_client=SyncClient(), run_in_thread=executor) as client:
                await client.parse_dbc(simple_dbc)
                await client.set_properties([prop.to_dict()])
                await client.start_stream()
                before = executor.ran
                main = _main_task()
                executor.cancel_at(main, after=CallCount(2))
                with pytest.raises(asyncio.CancelledError):
                    _ = await client.send_frames(_make_frames(50))
                _ = main.uncancel()
                assert executor.ran - before == 2
                result = await client.end_stream()
                assert result["status"] == "complete"

        asyncio.run(_run())

    def test_cancel_during_close_does_not_leak_state(self) -> None:
        """A cancellation delivered while ``close`` waits must not drop the FFI release.

        ``close()`` wraps its ``asyncio.to_thread(self._sync.close)`` in
        ``asyncio.shield``.  The cancel lands as the close is queued: the awaiter
        is cancelled, and the shielded call still gets its turn and runs, so the
        session is released.  Without the shield the cancel would drop the queued
        call, as an executor drops a job cancelled before its turn.
        """
        executor = TurnExecutor()

        async def _run() -> None:
            sync = SyncClient()
            # AsyncClient is double-close-safe, so the implicit __aexit__ at the
            # end of the block is a no-op after the cancelled explicit close.
            async with AsyncClient(sync_client=sync, run_in_thread=executor) as client:
                assert not sync.is_closed
                main = _main_task()
                executor.cancel_at(main, after=CallCount(0))
                with pytest.raises(asyncio.CancelledError):
                    await client.close()
                _ = main.uncancel()
                # The shielded call was queued before this task's next turn, and
                # the loop runs ready callbacks in the order they were queued.
                await asyncio.sleep(0)
                assert sync.is_closed, "FFI session must be released even when close was cancelled"

        asyncio.run(_run())


# =============================================================================
# Async iter cancellation — `asyncio.timeout` around `async for ... in iter`
# =============================================================================


class TestAsyncIterCancellation:
    """Async iter ops surface ``CancelledError`` at the yield boundary."""

    def test_timeout_during_iter(self, simple_dbc: DBCDefinition) -> None:
        """A timeout during ``async for`` surfaces as ``TimeoutError`` and leaves the stream usable.

        ``asyncio.timeout(0)`` fires on the first frame's turn, which is dropped
        before it runs; nothing was consumed, and ``end_stream`` completes.
        """
        prop = Signal("TestSignal").less_than(1000).always()
        executor = TurnExecutor()

        async def _run() -> None:
            async with AsyncClient(sync_client=SyncClient(), run_in_thread=executor) as client:
                await client.parse_dbc(simple_dbc)
                await client.set_properties([prop.to_dict()])
                await client.start_stream()
                consumed = 0
                with pytest.raises(TimeoutError):
                    async with asyncio.timeout(0):
                        consumed = await _consume_iter(client.send_frames_iter(_make_frames(50)))
                assert consumed == 0
                result = await client.end_stream()
                assert result["status"] == "complete"

        asyncio.run(_run())

    def test_async_iter_yields_frame_result_with_index(
        self,
        simple_dbc: DBCDefinition,
    ) -> None:
        """Smoke: full async-iter consumption yields one FrameResult per frame."""
        prop = Signal("TestSignal").less_than(1000).always()

        async def _run() -> list[FrameResult]:
            async with AsyncClient(
                sync_client=SyncClient(), run_in_thread=TurnExecutor()
            ) as client:
                await client.parse_dbc(simple_dbc)
                await client.set_properties([prop.to_dict()])
                await client.start_stream()
                results: list[FrameResult] = [
                    r async for r in client.send_frames_iter(_make_frames(5))
                ]
                await client.end_stream()
                return results

        results = asyncio.run(_run())
        assert len(results) == 5
        assert [r.frame_index for r in results] == [0, 1, 2, 3, 4]
        assert [r.timestamp for r in results] == [1000, 2000, 3000, 4000, 5000]


# =============================================================================
# TurnExecutor — the public stand-in for asyncio.to_thread
# =============================================================================


# The name a stand-in call records, so a test reads which calls were made.
CallName = NewType("CallName", str)


class TestTurnExecutor:
    """``TurnExecutor`` runs each call at its turn, and drops one cancelled before it."""

    def test_a_call_runs_at_its_turn_and_returns_its_result(self) -> None:
        """The call's value comes back, and the call is counted as run."""
        executor = TurnExecutor()

        async def _run() -> CallCount:
            assert await executor(len, "abc") == len("abc")
            return executor.ran

        assert asyncio.run(_run()) == CallCount(1)

    def test_a_call_cancelled_before_its_turn_never_runs(self) -> None:
        """A cancellation named for the next call drops it: the call is never made."""
        executor = TurnExecutor()
        made: list[CallName] = []

        async def _run() -> None:
            main = _main_task()
            executor.cancel_at(main, after=CallCount(0))
            with pytest.raises(asyncio.CancelledError):
                await executor(made.append, CallName("dropped"))
            _ = main.uncancel()

        asyncio.run(_run())
        assert not made
        assert executor.ran == CallCount(0)

    def test_the_cancellation_lands_on_the_named_call(self) -> None:
        """Calls before the named one run; the named one is dropped."""
        executor = TurnExecutor()
        made: list[CallName] = []

        async def _run() -> None:
            main = _main_task()
            executor.cancel_at(main, after=CallCount(1))
            await executor(made.append, CallName("first"))
            with pytest.raises(asyncio.CancelledError):
                await executor(made.append, CallName("second"))
            _ = main.uncancel()

        asyncio.run(_run())
        assert made == ["first"]

    def test_every_async_call_goes_through_run_in_thread(self, simple_dbc: DBCDefinition) -> None:
        """Each async method hands its sync calls to ``run_in_thread``, the shielded ones included.

        A method left on ``asyncio.to_thread`` would escape the stand-in, and with
        it the order and the cancellation a test drives, so each method's calls
        are counted on the executor: one per method, one per frame for the
        iterator.
        """
        executor = TurnExecutor()
        frame = _make_frames(1)[0]
        data = bytes(frame.data)
        signals = {"TestSignal": 1}
        prop = Signal("TestSignal").less_than(1000).always()

        async def _queued_by[T](call: Awaitable[T]) -> CallCount:
            before = executor.queued
            _ = await call
            return CallCount(executor.queued - before)

        async def _run() -> dict[CallName, CallCount]:
            entering = executor.queued
            async with AsyncClient(sync_client=SyncClient(), run_in_thread=executor) as client:
                counts = {CallName("__aenter__"): CallCount(executor.queued - entering)}
                before = executor.queued
                text = (await client.format_dbc_text(simple_dbc))["text"]
                counts[CallName("format_dbc_text")] = CallCount(executor.queued - before)
                counts |= {
                    CallName("parse_dbc_text"): await _queued_by(client.parse_dbc_text(text)),
                    CallName("parse_dbc"): await _queued_by(client.parse_dbc(simple_dbc)),
                    CallName("validate_dbc"): await _queued_by(client.validate_dbc(simple_dbc)),
                    CallName("format_dbc"): await _queued_by(client.format_dbc()),
                    CallName("set_properties"): await _queued_by(
                        client.set_properties([prop.to_dict()])
                    ),
                    CallName("add_checks"): await _queued_by(client.add_checks([])),
                    CallName("extract_signals"): await _queued_by(
                        client.extract_signals(frame.can_id, frame.dlc, data)
                    ),
                    CallName("build_frame"): await _queued_by(
                        client.build_frame(frame.can_id, frame.dlc, signals)
                    ),
                    CallName("update_frame"): await _queued_by(
                        client.update_frame(frame.can_id, frame.dlc, data, signals)
                    ),
                    CallName("start_stream"): await _queued_by(client.start_stream()),
                    CallName("send_frame"): await _queued_by(
                        client.send_frame(frame.timestamp, frame.can_id, frame.dlc, data)
                    ),
                    CallName("send_frames"): await _queued_by(
                        client.send_frames(_make_frames(2, start_ts=2000))
                    ),
                    CallName("send_frames_iter"): await _queued_by(
                        _consume_iter(client.send_frames_iter(_make_frames(2, start_ts=4000)))
                    ),
                    CallName("send_error"): await _queued_by(client.send_error(6000)),
                    CallName("send_remote"): await _queued_by(
                        client.send_remote(7000, frame.can_id)
                    ),
                    CallName("end_stream"): await _queued_by(client.end_stream()),
                    CallName("close"): await _queued_by(client.close()),
                }
                leaving = executor.queued
            counts[CallName("__aexit__")] = CallCount(executor.queued - leaving)
            return counts

        counts = asyncio.run(_run())
        twice = {CallName("send_frames"), CallName("send_frames_iter")}
        assert counts == {name: CallCount(2 if name in twice else 1) for name in counts}

    def test_a_failing_call_hands_its_exception_to_the_awaiter(self) -> None:
        """An exception the call raises reaches the awaiter, as ``asyncio.to_thread`` hands it."""
        executor = TurnExecutor()

        async def _run() -> None:
            with pytest.raises(ValueError, match="invalid literal"):
                _ = await executor(int, "x")

        asyncio.run(_run())


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
        """FrameResult.violation returns the first fails entry in the batch.

        ``FrameResult.response`` carries the per-frame
        ``PropertyBatchResponse``; ``.violation`` extracts
        the first ``status == "fails"`` entry rather than the response
        as a whole.
        """
        viol_entry: PropertyResultEntry = {
            "type": "property",
            "status": "fails",
            "property_index": 0,
            "timestamp": 1000,
        }
        batch_response: PropertyBatchResponse = {
            "type": "property_batch",
            "results": [viol_entry],
        }
        r = FrameResult(
            frame_index=0,
            timestamp=1000,
            can_id=0x100,
            extended=False,
            response=batch_response,
        )
        assert r.violation == viol_entry
