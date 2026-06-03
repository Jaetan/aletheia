# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
"""Async mirror of :class:`aletheia.AletheiaClient`.

Each operation method delegates to its sync counterpart on a background
thread via :func:`asyncio.to_thread`; the resulting coroutine is
cancellable through the standard ``asyncio.CancelledError`` mechanism.
See ``docs/architecture/CANCELLATION.md`` for the full contract.

Concurrency policy: one ``aletheia.asyncio.AletheiaClient`` instance
serves exactly **one asyncio task at a time**. Concurrent access from
multiple tasks corrupts the underlying ``StreamState`` — pool clients
per task, do not share. This mirrors ``httpx.AsyncClient`` and is
explicit in CANCELLATION.md §5.3.

Throughput note: every method is one ``asyncio.to_thread`` round-trip,
which is the cost of cancel-mid-batch responsiveness. For pure
throughput on already-materialized data, the sync client's
``send_frames`` is faster — async exists for the responsive-cancellation
use case, not as a faster path.
"""

from __future__ import annotations

import asyncio
from typing import TYPE_CHECKING, Self, override

from aletheia.client._client import AletheiaClient as _SyncClient
from aletheia.client._types import (
    CANFrameTuple,
    FrameResult,
    SignalExtractionResult,
    call_send_frame,
)

if TYPE_CHECKING:
    from collections.abc import AsyncGenerator, Iterable, Mapping
    from fractions import Fraction
    from types import TracebackType

    from aletheia.checks import CheckResult
    from aletheia.client._backend import Backend
    from aletheia.protocols import (
        AckResponse,
        CompleteResponse,
        DBCDefinition,
        DLCCode,
        ErrorResponse,
        LTLFormula,
        ParsedDBCResponse,
        PropertyBatchResponse,
        SuccessResponse,
        ValidationResponse,
    )


class AletheiaClient:  # pylint: disable=too-many-public-methods
    """Asynchronous Aletheia client.

    Every operation is an ``async def`` that wraps the sync FFI call
    through :func:`asyncio.to_thread`. Cancelling the awaiting task
    raises :class:`asyncio.CancelledError` at the next ``await`` point.

    The shape of the API matches the sync ``AletheiaClient`` exactly,
    method-for-method, so user code can switch sync↔async by changing
    the import without touching call sites.
    """

    def __init__(
        self,
        default_checks: list[CheckResult] | None = None,
        rts_cores: int = 1,
        sync_client: _SyncClient | None = None,
        *,
        backend: Backend | None = None,
    ) -> None:
        """See :class:`aletheia.AletheiaClient.__init__`.

        The constructor itself is synchronous — DBC + property setup
        happens later via ``await client.parse_dbc(...)`` and friends.

        ``sync_client`` is an injection seam for tests:
        when provided, the AsyncClient wraps that pre-built sync client
        instead of constructing one internally.  Callers passing
        ``sync_client=...`` are responsible for ``default_checks`` /
        ``rts_cores`` configuration on the injected instance; the
        kwargs of the same names (and ``backend=``) are ignored when
        ``sync_client`` is non-None.  See ``aletheia.asyncio.testing.gated_backend``
        for the canonical use case (deterministic cancellation tests
        via the public Backend DI seam).

        ``backend`` mirrors the sync
        constructor's keyword-only ``backend=`` kwarg, restoring
        symmetry promised in this module's docstring header ("user
        code can switch sync↔async by changing the import without
        touching call sites").  Forwarded into the internal sync
        construction; mutually exclusive with ``sync_client`` (use
        one or the other).
        """
        if sync_client is not None:
            self._sync = sync_client
        else:
            self._sync = _SyncClient(
                default_checks=default_checks,
                rts_cores=rts_cores,
                backend=backend,
            )

    async def __aenter__(self) -> Self:
        """Load the FFI library + initialize RTS on a background thread.

        Wrapped in :func:`asyncio.shield` so a cancellation on the awaiting
        task cannot leave RTS state half-initialized — the underlying
        ``hs_init`` call is not interruptible cooperatively (CANCELLATION.md
        §5.1), and a partial init would orphan the StablePtr.  Cancellation
        delivered during init still propagates: the shield only protects the
        init from being cancelled mid-call; it doesn't suppress.
        """
        await asyncio.shield(asyncio.to_thread(self._sync.__enter__))
        return self

    async def __aexit__(
        self,
        exc_type: type[BaseException] | None,
        exc_val: BaseException | None,
        exc_tb: TracebackType | None,
    ) -> None:
        """Free state and release the RTS reference.

        Wrapped in :func:`asyncio.shield` so cancellation cannot leak the
        FFI session — partial close would leave the StablePtr alive and the
        backing IORef unreachable.  The shield delays the CancelledError
        delivery until after the close has completed (see CANCELLATION.md
        §5.1 — "teardown is best-effort, idempotent, and double-close safe;
        cancellation cannot preempt the GHC RTS").
        """
        del exc_type, exc_val, exc_tb
        await asyncio.shield(asyncio.to_thread(self._sync.close))

    async def close(self) -> None:
        """Free state and release RTS reference. Same uncancellable contract as ``__aexit__``."""
        await asyncio.shield(asyncio.to_thread(self._sync.close))

    @property
    def is_closed(self) -> bool:
        """Whether :meth:`close` has been called.

        Cross-binding parity with sync :class:`aletheia.AletheiaClient.is_closed`
        and Go ``Client.IsClosed()``.
        """
        return self._sync.is_closed

    # =========================================================================
    # DBC and Properties
    # =========================================================================

    async def parse_dbc(
        self,
        dbc: DBCDefinition,
    ) -> ParsedDBCResponse | ErrorResponse:
        """Async mirror of :meth:`aletheia.AletheiaClient.parse_dbc`."""
        return await asyncio.to_thread(self._sync.parse_dbc, dbc)

    async def parse_dbc_text(
        self,
        text: str,
    ) -> ParsedDBCResponse | ErrorResponse:
        """Async mirror of :meth:`aletheia.AletheiaClient.parse_dbc_text`."""
        return await asyncio.to_thread(self._sync.parse_dbc_text, text)

    async def validate_dbc(self, dbc: DBCDefinition) -> ValidationResponse:
        """Async mirror of :meth:`aletheia.AletheiaClient.validate_dbc`."""
        return await asyncio.to_thread(self._sync.validate_dbc, dbc)

    async def format_dbc(self) -> DBCDefinition:
        """Async mirror of :meth:`aletheia.AletheiaClient.format_dbc`."""
        return await asyncio.to_thread(self._sync.format_dbc)

    async def format_dbc_text(self, dbc: DBCDefinition) -> str:
        """Async mirror of :meth:`aletheia.AletheiaClient.format_dbc_text`."""
        return await asyncio.to_thread(self._sync.format_dbc_text, dbc)

    async def set_properties(
        self,
        properties: list[LTLFormula],
    ) -> SuccessResponse | ErrorResponse:
        """Async mirror of :meth:`aletheia.AletheiaClient.set_properties`."""
        return await asyncio.to_thread(self._sync.set_properties, properties)

    async def add_checks(
        self,
        checks: list[CheckResult],
    ) -> SuccessResponse | ErrorResponse:
        """Async mirror of :meth:`aletheia.AletheiaClient.add_checks`."""
        return await asyncio.to_thread(self._sync.add_checks, checks)

    # =========================================================================
    # Streaming LTL Checking
    # =========================================================================

    async def start_stream(self) -> SuccessResponse | ErrorResponse:
        """Async mirror of :meth:`aletheia.AletheiaClient.start_stream`."""
        return await asyncio.to_thread(self._sync.start_stream)

    async def send_frame(  # noqa: PLR0913  # pylint: disable=too-many-arguments
        self,
        timestamp: int,
        can_id: int,
        dlc: DLCCode,
        data: bytes | bytearray,
        *,
        extended: bool = False,
        brs: bool | None = None,
        esi: bool | None = None,
    ) -> AckResponse | PropertyBatchResponse | ErrorResponse:
        """Async mirror of :meth:`aletheia.AletheiaClient.send_frame`."""
        return await asyncio.to_thread(
            self._sync.send_frame,
            timestamp,
            can_id,
            dlc,
            data,
            extended=extended,
            brs=brs,
            esi=esi,
        )

    async def send_frames(
        self,
        frames: list[CANFrameTuple],
    ) -> list[AckResponse | PropertyBatchResponse]:
        """Async batch send; cancels at frame-boundary ``await`` points.

        Each frame is one ``asyncio.to_thread`` round-trip, so cancellation
        fires between frames as ``asyncio.CancelledError`` (reraised
        verbatim — the committed prefix lives in stream state, not the
        exception). ``BatchError`` on non-cancellation errors carries the
        committed prefix in ``partial_results``; see CANCELLATION.md §3.1.
        """
        # CancelledError is BaseException since 3.8 → not caught by `except
        # Exception` inside call_send_frame, propagates verbatim. Stream state
        # holds the committed prefix; bundling it would invite swallowing.
        results: list[AckResponse | PropertyBatchResponse] = []
        for i, frame in enumerate(frames):
            results.append(
                await asyncio.to_thread(
                    call_send_frame,
                    self._sync.send_frame,
                    i,
                    frame,
                    results,
                )
            )
        return results

    async def send_frames_iter(
        self,
        frames: Iterable[CANFrameTuple],
    ) -> AsyncGenerator[FrameResult]:
        """Async iter analog of :meth:`aletheia.AletheiaClient.send_frames_iter`.

        Cancels via ``asyncio.CancelledError`` at the per-frame ``await``
        boundary; the partial-results contract (yielded prefix is
        committed; ``BatchError.partial_results`` is empty on non-cancel
        errors) matches the sync iter exactly.
        """
        # CancelledError propagates verbatim (BaseException since 3.8 → not
        # caught by `except Exception` inside call_send_frame). Already-
        # yielded results are durable in the consumer's hands.
        for i, frame in enumerate(frames):
            resp = await asyncio.to_thread(
                call_send_frame,
                self._sync.send_frame,
                i,
                frame,
                [],
            )
            # R0801 false positive: populating ``FrameResult`` from a frame is
            # the same field mapping as the sync streaming generator; both run
            # per-frame, so a shared helper would add a call per yielded frame.
            # pylint: disable=duplicate-code
            yield FrameResult(
                frame_index=i,
                timestamp=frame.timestamp,
                can_id=frame.can_id,
                extended=frame.extended,
                response=resp,
            )
            # pylint: enable=duplicate-code

    async def send_error(self, timestamp: int) -> AckResponse:
        """Async mirror of :meth:`aletheia.AletheiaClient.send_error`."""
        return await asyncio.to_thread(self._sync.send_error, timestamp)

    async def send_remote(
        self,
        timestamp: int,
        can_id: int,
        *,
        extended: bool = False,
    ) -> AckResponse:
        """Async mirror of :meth:`aletheia.AletheiaClient.send_remote`."""
        return await asyncio.to_thread(
            self._sync.send_remote,
            timestamp,
            can_id,
            extended=extended,
        )

    async def end_stream(self) -> CompleteResponse | ErrorResponse:
        """Async mirror of :meth:`aletheia.AletheiaClient.end_stream`."""
        return await asyncio.to_thread(self._sync.end_stream)

    # =========================================================================
    # Signal operations
    # =========================================================================

    async def extract_signals(
        self,
        can_id: int,
        dlc: DLCCode,
        data: bytes | bytearray,
        *,
        extended: bool = False,
    ) -> SignalExtractionResult:
        """Async mirror of :meth:`aletheia.AletheiaClient.extract_signals`."""
        return await asyncio.to_thread(
            self._sync.extract_signals,
            can_id,
            dlc,
            data,
            extended=extended,
        )

    async def update_frame(  # pylint: disable=too-many-arguments
        self,
        can_id: int,
        dlc: DLCCode,
        frame: bytes | bytearray,
        signals: Mapping[str, float | Fraction],
        *,
        extended: bool = False,
    ) -> bytearray:
        """Async mirror of :meth:`aletheia.AletheiaClient.update_frame`."""
        return await asyncio.to_thread(
            self._sync.update_frame,
            can_id,
            dlc,
            frame,
            signals,
            extended=extended,
        )

    async def build_frame(
        self,
        can_id: int,
        dlc: DLCCode,
        signals: Mapping[str, float | Fraction],
        *,
        extended: bool = False,
    ) -> bytearray:
        """Async mirror of :meth:`aletheia.AletheiaClient.build_frame`."""
        return await asyncio.to_thread(
            self._sync.build_frame,
            can_id,
            dlc,
            signals,
            extended=extended,
        )

    @override
    def __repr__(self) -> str:
        return f"aletheia.asyncio.AletheiaClient(sync={self._sync!r})"
