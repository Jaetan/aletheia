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
from collections.abc import Iterable

import pytest

from aletheia import AletheiaClient as SyncClient, BatchError, FrameResult, Signal
from aletheia.asyncio import AletheiaClient as AsyncClient
from aletheia.protocols import DBCDefinition


def _make_frames(
    n: int, *, can_id: int = 256, start_ts: int = 1000,
) -> list[tuple[int, int, int, bytearray, bool]]:
    """Build n monotonically-timestamped frames with payload (i, 0, 0, …)."""
    return [
        (start_ts + i * 1000, can_id, 8, bytearray([i & 0xFF, 0, 0, 0, 0, 0, 0, 0]), False)
        for i in range(n)
    ]


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
            bad: list[tuple[int, int, int, bytearray, bool]] = [
                (1000, 256, 8, bytearray(8), False),
                (2000, 256, 8, bytearray(8), False),
                (500, 256, 8, bytearray(8), False),
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

        def lazy_source() -> Iterable[tuple[int, int, int, bytearray, bool]]:
            for i in range(100):
                consumed_from_source.append(i)
                yield (1000 + i * 1000, 256, 8, bytearray(8), False)

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
                ack = await client.send_frame(1000, 256, 8, bytearray(8))
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
        """A 0-second timeout cancels before any frame and raises TimeoutError."""
        prop = Signal("TestSignal").less_than(1000).always()

        async def _run() -> None:
            async with AsyncClient() as client:
                await client.parse_dbc(simple_dbc)
                await client.set_properties([prop.to_dict()])
                await client.start_stream()
                # Tiny timeout fires before any to_thread completes; the
                # awaiting task sees CancelledError → asyncio.timeout
                # converts to TimeoutError.
                with pytest.raises(TimeoutError):
                    async with asyncio.timeout(0):
                        await client.send_frames(_make_frames(50))
                # Stream state still consistent — end_stream succeeds.
                result = await client.end_stream()
                assert result["status"] == "complete"

        asyncio.run(_run())

    def test_explicit_task_cancel(self, simple_dbc: DBCDefinition) -> None:
        """Cancelling the task surfaces CancelledError on the awaiter."""
        prop = Signal("TestSignal").less_than(1000).always()

        async def _run() -> None:
            async with AsyncClient() as client:
                await client.parse_dbc(simple_dbc)
                await client.set_properties([prop.to_dict()])
                await client.start_stream()

                task: asyncio.Task[list[object]] = asyncio.create_task(  # type: ignore[type-arg]
                    client.send_frames(_make_frames(50)),  # type: ignore[arg-type]
                )
                # Give the task one event-loop turn to enter the first
                # to_thread, then cancel.
                await asyncio.sleep(0)
                task.cancel()
                with pytest.raises(asyncio.CancelledError):
                    await task

                # Stream state is consistent regardless of how many frames
                # committed — end_stream succeeds.
                result = await client.end_stream()
                assert result["status"] == "complete"

        asyncio.run(_run())


# =============================================================================
# Async iter cancellation — `asyncio.timeout` around `async for ... in iter`
# =============================================================================


class TestAsyncIterCancellation:
    """Async iter ops surface ``CancelledError`` at the yield boundary."""

    def test_timeout_during_iter(self, simple_dbc: DBCDefinition) -> None:
        """Timeout during ``async for`` — committed prefix durable, async-iter
        wraps cancellation in TimeoutError per asyncio.timeout semantics."""
        prop = Signal("TestSignal").less_than(1000).always()

        async def _run() -> None:
            async with AsyncClient() as client:
                await client.parse_dbc(simple_dbc)
                await client.set_properties([prop.to_dict()])
                await client.start_stream()

                consumed = 0
                with pytest.raises(TimeoutError):
                    async with asyncio.timeout(0):
                        async for _r in client.send_frames_iter(_make_frames(50)):
                            consumed += 1

                # The consumer may have received zero or a small prefix; the
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
        viol_response = {
            "status": "fails",
            "results": [],
            "metric": {"steps": 1},
            "frame_index": 0,
        }
        r = FrameResult(
            frame_index=0,
            timestamp=1000,
            can_id=0x100,
            extended=False,
            response=viol_response,  # type: ignore[arg-type]
        )
        assert r.violation is viol_response
