# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
"""Streaming / frame-I/O mixin for :class:`aletheia.AletheiaClient`.

Hosts ``start_stream`` / ``send_frame`` / ``send_frames`` /
``send_frames_iter`` / ``send_error`` / ``send_remote`` / ``end_stream`` and
their violation-enrichment helpers, so the setup-and-DBC core in ``_client.py``
stays under the configured module-size threshold.  Pure split -- no behavioral
change.  The mixin relies on the host class providing the private state surface
(``_backend`` / ``_state`` / ``_caches`` / ``_diags`` / ``_send_frame_binary``)
and the ``extract_signals`` method (implemented by :class:`SignalOpsMixin`);
the class-level annotations + abstract stub below declare that surface so
pyright trusts the access paths while pylint sees legitimate forward
declarations.
"""

from __future__ import annotations

import logging
from abc import ABC, abstractmethod
from typing import TYPE_CHECKING, cast

from aletheia.client._client_bin import FrameIdentity
from aletheia.client._enrichment import format_enriched_reason
from aletheia.client._ffi import parse_json_object
from aletheia.client._log import LogEvent, log_event
from aletheia.client._response_parsers import (
    build_error_response,
    parse_event_response,
    parse_finalization_results,
    parse_frame_response,
    parse_success_or_error,
)
from aletheia.client._types import (
    MAX_EXTRACT_CACHE,
    AletheiaError,
    CANFrameTuple,
    FrameResult,
    PropertyDiagnostic,
    ProtocolError,
    SignalExtractionResult,
    StateError,
    StreamCaches,
    ValidationError,
    call_send_frame,
    make_frame_result,
    validate_can_id,
    validate_payload_length,
)

if TYPE_CHECKING:
    from collections.abc import Callable, Generator, Iterable
    from fractions import Fraction

    from aletheia.client._backend import Backend
    from aletheia.protocols import (
        AckResponse,
        CompleteResponse,
        CompleteWarning,
        DLCCode,
        ErrorResponse,
        PropertyBatchResponse,
        PropertyResultEntry,
        RationalNumber,
        Response,
        SuccessResponse,
    )


_logger = logging.getLogger("aletheia")


def _rational_index(r: RationalNumber, context: str) -> int:
    """Convert a rational property_index to int, raising on zero denominator."""
    if r["denominator"] == 0:
        msg = f"Zero denominator in {context} property_index"
        raise ProtocolError(msg)
    return r["numerator"] // r["denominator"]


class StreamingMixin(ABC):
    """Streaming-mode frame I/O and violation enrichment.

    Mixed into :class:`aletheia.AletheiaClient` alongside
    :class:`SignalOpsMixin`.  Bases are ordered ``(SignalOpsMixin,
    StreamingMixin)`` so the concrete ``extract_signals`` precedes this
    abstract stub in the MRO (otherwise the host class would stay abstract).
    """

    _backend: Backend | None
    _state: int | None
    _caches: StreamCaches
    _diags: dict[int, PropertyDiagnostic]
    _send_frame_binary: Callable[..., bytes]

    @abstractmethod
    def extract_signals(
        self,
        can_id: int,
        dlc: DLCCode,
        data: bytes | bytearray,
        *,
        extended: bool = False,
    ) -> SignalExtractionResult:
        """Extract all signals from a frame (provided by SignalOpsMixin)."""

    def start_stream(self) -> SuccessResponse | ErrorResponse:
        """Start streaming mode for incremental LTL checking.

        Returns:
            SuccessResponse or ErrorResponse

        """
        if self._backend is None or self._state is None:
            msg = "Client not initialized — use 'with' statement"
            raise StateError(msg)
        response_bytes = self._backend.start_stream_binary(self._state)
        response = parse_success_or_error(
            cast("Response", parse_json_object(response_bytes.decode("utf-8"))),
        )
        if response["status"] == "success":
            self._caches.clear()
            log_event(_logger, logging.INFO, LogEvent.STREAM_STARTED)
        return response

    def _enrich_violation(
        self,
        result: PropertyResultEntry,
        frame_id: FrameIdentity,
        data: bytes | bytearray,
    ) -> None:
        """Enrich one violation entry with signal diagnostics (in-place).

        Takes one inner ``PropertyResultEntry`` from
        ``PropertyBatchResponse.results``; caller filters to fails entries.
        """
        if not self._diags:
            return
        idx = _rational_index(result["property_index"], "violation")
        diag = self._diags.get(idx)
        if diag is None:
            log_event(
                _logger,
                logging.WARNING,
                LogEvent.ENRICHMENT_PROPERTY_INDEX_OOB,
                index=idx,
                count=len(self._diags),
            )
            return

        # Extract signal values (cached, bounded).
        cache_key = (frame_id.can_id, frame_id.extended, bytes(data))
        extraction: SignalExtractionResult | None = self._caches.extraction.get(cache_key)
        if extraction is None:
            log_event(
                _logger,
                logging.DEBUG,
                LogEvent.CACHE_MISS,
                canId=frame_id.can_id,
                dlc=frame_id.dlc,
            )
            try:
                extraction = self.extract_signals(
                    can_id=frame_id.can_id,
                    dlc=frame_id.dlc,
                    data=data,
                    extended=frame_id.extended,
                )
                if len(self._caches.extraction) < MAX_EXTRACT_CACHE:
                    self._caches.extraction[cache_key] = extraction
                else:
                    log_event(
                        _logger,
                        logging.WARNING,
                        LogEvent.CACHE_FULL,
                        size=len(self._caches.extraction),
                    )
            except (AletheiaError, ValueError) as exc:
                # Enrichment is best-effort — the frame still streamed and the
                # core verdict is authoritative.  Emit a single-line warning
                # with the exception message; dropping ``exc_info`` keeps
                # production logs scannable (traceback-worthy paths use
                # ``_logger.error(..., exc_info=True)`` instead).
                log_event(
                    _logger,
                    logging.WARNING,
                    LogEvent.ENRICHMENT_EXTRACTION_FAILED,
                    canId=frame_id.can_id,
                    error=str(exc),
                )
        else:
            log_event(
                _logger,
                logging.DEBUG,
                LogEvent.CACHE_HIT,
                canId=frame_id.can_id,
                dlc=frame_id.dlc,
            )

        values: dict[str, Fraction | None] = {}
        if extraction is not None:
            for sig in diag.signals:
                val = extraction.values.get(sig)
                if val is not None:
                    values[sig] = val

        core_reason = result.get("reason", "")
        result["enrichment"] = {
            "signals": values,
            "formula_desc": diag.formula_desc,
            "enriched_reason": format_enriched_reason(diag, values, core_reason),
            "core_reason": core_reason,
        }

    # Pre-encoded ack-response shapes — compact form from the binary FFI
    # path; post-colon-space form from the JSON FFI path (what `json.dumps`
    # emits by default).  Hoisted to a class const so the streaming hot
    # path's membership test doesn't allocate a fresh 2-tuple per frame.
    _ACK_RESPONSES = (b'{"status":"ack"}', b'{"status": "ack"}')

    def send_frame(  # pylint: disable=too-many-arguments  # noqa: PLR0913
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
        """Send a CAN frame for incremental LTL checking.

        If properties have been set via ``set_properties()``, violation
        responses are automatically enriched with an ``enrichment`` field
        containing ``signals``, ``formula_desc``, ``enriched_reason``, and
        ``core_reason``.

        Args:
            timestamp: Timestamp in microseconds
            can_id: CAN ID (11-bit standard or 29-bit extended)
            dlc: DLC code (0-8 for CAN 2.0B, 0-15 for CAN-FD)
            data: Frame payload
            extended: True for 29-bit extended CAN ID, False for 11-bit standard
            brs: CAN-FD Bit Rate Switch (ISO 11898-1:2015 §10.4.2);
                ``None`` for CAN 2.0B. Pass-through metadata — not consumed
                by the kernel; see :class:`aletheia.CANFrameTuple`.
            esi: CAN-FD Error State Indicator (ISO 11898-1:2015 §10.4.3);
                same semantics and pass-through status as ``brs``.

        Returns:
            AckResponse, PropertyBatchResponse, or ErrorResponse

        """
        if self._backend is None or self._state is None:
            msg = "Client not initialized — use 'with' statement"
            raise StateError(msg)
        if timestamp < 0:
            msg = "timestamp must be non-negative"
            raise ValidationError(msg)
        validate_can_id(can_id, extended=extended)
        validate_payload_length(dlc, data)  # validates dlc is in [0, 15]

        # Use the bound method cached at __enter__ to dodge per-frame
        # attribute-lookup cost on ``self._backend.send_frame_binary``.
        #
        # R0801: these eight kwargs are ``send_frame_binary``'s wire signature,
        # restated wherever a frame crosses the backend boundary (here and the
        # testing double).  A forwarding helper only moves the kwarg list to its
        # call sites; a positional one re-trips PLR0913 on the eight fields (see
        # the testing backend's ``# noqa: PLR0913``) — so the duplication is
        # structural, not removable by extraction.  The cached bound method is
        # passed through unchanged, so this is not a perf trade-off.
        # pylint: disable=duplicate-code
        result_bytes = self._send_frame_binary(
            self._state,
            timestamp=timestamp,
            can_id=can_id,
            extended=extended,
            dlc=dlc,
            data=data,
            brs=brs,
            esi=esi,
        )
        # pylint: enable=duplicate-code

        # Track last frame per CAN ID for EOS enrichment.
        if self._diags:
            self._caches.last_frames[(can_id, extended)] = (dlc, bytearray(data))

        # Fast path: ack response (overwhelmingly common in streaming).
        # The `isEnabledFor` guard mirrors stdlib `Logger.debug` — kwargs
        # are eagerly evaluated, so without it the per-frame 4-field
        # dict still allocates even when `log_event` would short-circuit.
        if result_bytes in self._ACK_RESPONSES:
            if _logger.isEnabledFor(logging.DEBUG):
                log_event(
                    _logger,
                    logging.DEBUG,
                    LogEvent.FRAME_PROCESSED,
                    ts=timestamp,
                    canId=can_id,
                    extended=extended,
                    response="ack",
                )
            return {"status": "ack"}

        # Slow path: batched events / errors — full JSON parse.
        # Streaming PropertyResponse is a batch envelope
        # (type=property_batch + results[]); enrich each fails entry.
        response = cast("Response", parse_json_object(result_bytes.decode("utf-8")))
        result = parse_frame_response(response)
        if result.get("type") == "property_batch":
            batch = cast("PropertyBatchResponse", result)
            frame_id = FrameIdentity(can_id, extended, dlc)
            self._handle_property_batch(batch, frame_id, data, timestamp)
        elif _logger.isEnabledFor(logging.DEBUG):
            log_event(
                _logger,
                logging.DEBUG,
                LogEvent.FRAME_PROCESSED,
                ts=timestamp,
                canId=can_id,
                extended=extended,
                response=result.get("status", "unknown"),
            )
        return result

    def _handle_property_batch(
        self,
        batch: PropertyBatchResponse,
        frame_id: FrameIdentity,
        data: bytes | bytearray,
        timestamp: int,
    ) -> None:
        """Enrich each failing entry in a property-batch response (in place).

        Off the ack fast path — runs only when ``send_frame`` sees a
        ``property_batch`` envelope (a frame that produced verdicts); the
        ack-response path returns earlier without reaching here.
        """
        for entry in batch["results"]:
            if entry.get("status") == "fails":
                self._enrich_violation(entry, frame_id, data)
        if _logger.isEnabledFor(logging.DEBUG):
            log_event(
                _logger,
                logging.DEBUG,
                LogEvent.FRAME_PROCESSED,
                ts=timestamp,
                canId=frame_id.can_id,
                extended=frame_id.extended,
                response=(
                    "violation"
                    if any(e.get("status") == "fails" for e in batch["results"])
                    else "satisfaction"
                ),
            )

    def send_frames(
        self,
        frames: list[CANFrameTuple],
    ) -> list[AckResponse | PropertyBatchResponse]:
        """Send multiple CAN frames in a batch.

        Processing stops when ``send_frame`` returns an ``ErrorResponse``
        (e.g. non-monotonic timestamp) or raises a Python exception.
        The raised ``BatchError`` carries ``partial_results`` collected
        up to and including the error, plus the ``frame_index`` of the
        failing frame.

        Violations are normal return values and do not stop the batch.

        Args:
            frames: List of CANFrameTuple (timestamp, can_id, dlc, data, extended).

        Returns:
            List of AckResponse or PropertyBatchResponse (no ErrorResponse
            entries; those stop the batch and raise BatchError).

        Raises:
            BatchError: Wraps the underlying exception (or an ErrorResponse)
                and carries ``partial_results`` and ``frame_index``.

        """
        results: list[AckResponse | PropertyBatchResponse] = []
        for i, frame in enumerate(frames):
            results.append(call_send_frame(self.send_frame, i, frame, results))
        return results

    def send_frames_iter(
        self,
        frames: Iterable[CANFrameTuple],
    ) -> Generator[FrameResult]:
        """Send frames lazily, yielding per-frame ``FrameResult`` outcomes.

        Streams the source iterable one frame at a time — useful when the
        source is a live producer (queue, socket, generator) and full
        materialization is wasteful or impossible. Cancellation is observed
        at frame boundaries via the standard generator protocol: when the
        consumer breaks the ``for`` loop or calls ``.close()`` on the
        returned generator, the next yield raises ``GeneratorExit`` and the
        loop exits. Every ``FrameResult`` already yielded is committed and
        durable in the client's stream state — this is the
        commit-prefix-and-report contract from
        docs/architecture/CANCELLATION.md §3.1.

        Violations are normal yielded results (``result.violation is not
        None`` exposes the underlying ``PropertyBatchResponse``) and do
        not stop the iteration. ``send_frame`` errors raise ``BatchError``
        with ``partial_results=[]`` (the committed prefix was already
        yielded; duplicating would invite double-handling) and
        ``frame_index`` pointing at the offending frame.

        Args:
            frames: Iterable of ``CANFrameTuple``.

        Yields:
            ``FrameResult`` per accepted frame.

        Raises:
            BatchError: On non-cancellation errors (e.g., non-monotonic
                timestamp); ``partial_results`` is empty.

        """
        for i, frame in enumerate(frames):
            yield make_frame_result(i, frame, call_send_frame(self.send_frame, i, frame, []))

    def send_error(self, timestamp: int) -> AckResponse:
        """Send a CAN error event (no ID, no payload).

        Error frames signal a bus error detected by a CAN controller.
        They are acknowledged without LTL evaluation — error frames carry
        no payload for signal extraction.

        Args:
            timestamp: Timestamp in microseconds

        Returns:
            AckResponse on success.

        Raises:
            ProtocolError: If the Agda core rejects the event (e.g.
                non-monotonic timestamp).

        """
        if self._backend is None or self._state is None:
            msg = "Client not initialized — use 'with' statement"
            raise StateError(msg)
        if timestamp < 0:
            msg = "timestamp must be non-negative"
            raise ValidationError(msg)
        result_bytes = self._backend.send_error_binary(self._state, timestamp)
        if result_bytes in self._ACK_RESPONSES:
            log_event(
                _logger,
                logging.DEBUG,
                LogEvent.ERROR_EVENT_SENT,
                ts=timestamp,
                response="ack",
            )
            return {"status": "ack"}
        response = cast("Response", parse_json_object(result_bytes.decode("utf-8")))
        return parse_event_response(response, "error_event", timestamp)

    def send_remote(
        self,
        timestamp: int,
        can_id: int,
        *,
        extended: bool = False,
    ) -> AckResponse:
        """Send a CAN remote frame event (ID but no payload).

        Remote frames request transmission of the data frame with a matching
        ID (CAN 2.0B only; deprecated in CAN-FD). They are acknowledged
        without LTL evaluation.

        Args:
            timestamp: Timestamp in microseconds
            can_id: CAN ID (11-bit standard or 29-bit extended)
            extended: True for 29-bit extended CAN ID

        Returns:
            AckResponse on success.

        Raises:
            ProtocolError: If the Agda core rejects the event (e.g.
                non-monotonic timestamp).

        """
        if self._backend is None or self._state is None:
            msg = "Client not initialized — use 'with' statement"
            raise StateError(msg)
        if timestamp < 0:
            msg = "timestamp must be non-negative"
            raise ValidationError(msg)
        validate_can_id(can_id, extended=extended)
        result_bytes = self._backend.send_remote_binary(
            self._state,
            timestamp=timestamp,
            can_id=can_id,
            extended=extended,
        )
        if result_bytes in self._ACK_RESPONSES:
            log_event(
                _logger,
                logging.DEBUG,
                LogEvent.REMOTE_EVENT_SENT,
                ts=timestamp,
                canId=can_id,
                extended=extended,
                response="ack",
            )
            return {"status": "ack"}
        response = cast("Response", parse_json_object(result_bytes.decode("utf-8")))
        return parse_event_response(response, "remote_event", timestamp)

    def end_stream(self) -> CompleteResponse | ErrorResponse:
        """End streaming mode and finalize all properties.

        Returns:
            CompleteResponse with per-property finalization results, or
            ErrorResponse if not currently streaming.

        The ``results`` list contains one entry per property:
        - ``status="holds"`` if the property held on the finite trace
        - ``status="fails"`` if the property failed at end-of-stream
          (e.g., liveness never satisfied)
        - ``status="unresolved"`` if the property's verdict is Unknown
          (e.g., signal never observed — Kleene three-valued semantics)

        Failed and unresolved results are enriched with an ``enrichment``
        field containing ``signals``, ``formula_desc``, ``enriched_reason``,
        and ``core_reason`` when checks have been registered.

        """
        if self._backend is None or self._state is None:
            msg = "Client not initialized — use 'with' statement"
            raise StateError(msg)
        response_bytes = self._backend.end_stream_binary(self._state)
        response = cast("Response", parse_json_object(response_bytes.decode("utf-8")))
        status = response.get("status")

        if status == "complete":
            results = parse_finalization_results(
                response,
                self._enrich_finalization_result,
            )
            raw_warnings = cast("list[dict[str, object]]", response.get("warnings", []))
            warnings: list[CompleteWarning] = [
                {
                    "kind": cast("str", w.get("kind", "")),
                    "property_index": cast("int", w.get("property_index", 0)),
                    "detail": cast("str", w.get("detail", "")),
                }
                for w in raw_warnings
            ]
            num_fails = sum(1 for r in results if r["status"] == "fails")
            num_unresolved = sum(1 for r in results if r["status"] == "unresolved")
            self._caches.last_frames.clear()
            for w in warnings:
                if w["kind"] == "uncached_atom":
                    log_event(
                        _logger,
                        logging.WARNING,
                        LogEvent.ENDSTREAM_UNCACHED_ATOM,
                        property_index=w["property_index"],
                        detail=w["detail"],
                    )
            log_event(
                _logger,
                logging.INFO,
                LogEvent.STREAM_ENDED,
                numResults=len(results),
                numFails=num_fails,
                numUnresolved=num_unresolved,
                numWarnings=len(warnings),
            )
            return {"status": "complete", "results": results, "warnings": warnings}

        if status == "error":
            return build_error_response(response)

        msg = f"Unexpected response status: {status!r} (expected 'complete' or 'error')"
        raise ProtocolError(msg)

    def _extract_last_known_values(
        self,
        diag: PropertyDiagnostic,
    ) -> dict[str, Fraction | None]:
        """Extract signal values from last-seen frames for EOS enrichment."""
        if not self._caches.last_frames or not diag.signals:
            return {}
        wanted = set(diag.signals)
        values: dict[str, Fraction | None] = {}
        # Sort by (canID, extended) for deterministic enrichment output,
        # matching Go's explicit sort and C++'s std::map ordering.
        for (lf_id, lf_ext), (lf_dlc, lf_data) in sorted(
            self._caches.last_frames.items(),
            key=lambda item: (item[0][0], item[0][1]),
        ):
            try:
                extraction = self.extract_signals(
                    can_id=lf_id,
                    dlc=lf_dlc,
                    data=lf_data,
                    extended=lf_ext,
                )
            except (AletheiaError, ValueError) as exc:
                # Finalization enrichment is best-effort (mirrors the hot
                # path); keep the warning single-line so operators can grep
                # ``enrichment.extraction_failed`` without drowning in
                # tracebacks.
                log_event(
                    _logger,
                    logging.WARNING,
                    LogEvent.ENRICHMENT_EXTRACTION_FAILED,
                    canId=lf_id,
                    error=str(exc),
                )
                continue
            for sig in list(wanted):
                val = extraction.values.get(sig)
                if val is not None:
                    values[sig] = val
                    wanted.discard(sig)
            if not wanted:
                break
        return values

    def _enrich_finalization_result(
        self,
        result: PropertyResultEntry,
    ) -> None:
        """Enrich an end-of-stream violation with signal diagnostics."""
        if not self._diags:
            return
        idx = _rational_index(result["property_index"], "finalization")
        diag = self._diags.get(idx)
        if diag is None:
            log_event(
                _logger,
                logging.WARNING,
                LogEvent.ENRICHMENT_PROPERTY_INDEX_OOB,
                index=idx,
                count=len(self._diags),
            )
            return
        values = self._extract_last_known_values(diag)
        core_reason = result.get("reason", "")
        result["enrichment"] = {
            "signals": values,
            "formula_desc": diag.formula_desc,
            "enriched_reason": format_enriched_reason(diag, values, core_reason),
            "core_reason": core_reason,
        }
