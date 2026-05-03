"""AletheiaClient — streaming LTL checking and signal operations via FFI."""

from __future__ import annotations

import ctypes
import logging
from collections.abc import Mapping
from fractions import Fraction
from typing import TYPE_CHECKING, Self, override, cast

from ..protocols import (
    DBCDefinition,
    LTLFormula,
    Command,
    Response,
    RationalNumber,
    ParseDBCCommand,
    ParseDBCTextCommand,
    SetPropertiesCommand,
    ValidateDBCCommand,
    SuccessResponse,
    AckResponse,
    PropertyViolationResponse,
    PropertyResultEntry,
    CompleteResponse,
    ErrorResponse,
    ValidationResponse,
    ParsedDBCResponse,
    is_str_dict,
    is_object_list,
)
from ._client_bin import BinaryFFI, FrameIdentity, SignalValues
from ._enrichment import build_diagnostic, format_enriched_reason
from ._ffi import (
    parse_json_object,
    RTSState,
    find_ffi_library,
    configure_ffi_signatures,
)
from ._helpers import (
    coerce_to_rational,
    dump_json,
    normalize_dbc,
    parse_absent_list,
    parse_errors_list,
    parse_values_list,
)
from ._log import LogEvent, log_event
from ._response_parsers import (
    build_error_response,
    parse_event_response,
    parse_finalization_results,
    parse_frame_response,
    parse_parsed_dbc_response,
    parse_success_or_error,
    validate_issue_severities,
)
from ._types import (
    AletheiaError,
    BatchError,
    CANFrameTuple,
    ProcessError,
    ProtocolError,
    SignalExtractionResult,
    PropertyDiagnostic,
    SignalLookup,
    StreamCaches,
    MAX_EXTRACT_CACHE,
    dlc_to_bytes,
    validate_can_id,
)

if TYPE_CHECKING:
    from ..checks import CheckResult

_logger = logging.getLogger("aletheia")


def _rational_index(r: RationalNumber, context: str) -> int:
    """Convert a rational property_index to int, raising on zero denominator."""
    if r["denominator"] == 0:
        raise ProtocolError(f"Zero denominator in {context} property_index")
    return r["numerator"] // r["denominator"]


class AletheiaClient:
    """Client for streaming LTL checking and signal operations.

    Uses ctypes to load libaletheia-ffi.so and call Haskell/Agda functions
    directly via FFI — no subprocess overhead.

    Protocol state machine:
    1. parse_dbc() - Load DBC definition (required first)
    2. Signal operations available anytime after DBC loaded:
       - extract_signals() - Extract all signals from a frame
       - update_frame() - Update specific signals in a frame
       - build_frame() - Build a frame from signal values
       - format_dbc() - Export currently-loaded DBC as JSON
       - validate_dbc() - Validate a DBC for structural issues
    3. Streaming LTL checking:
       - set_properties() - Set LTL properties (auto-derives diagnostics)
       - start_stream() - Enter streaming mode
       - send_frame() - Send frames for incremental checking
       - end_stream() - Exit streaming mode

    Signal operations work both inside and outside streaming mode.

    Thread safety: not thread-safe. Create one client per thread. The
    underlying GHC RTS is ref-counted and shared safely across instances.
    """

    def __init__(
        self,
        default_checks: list[CheckResult] | None = None,
        rts_cores: int = 1,
    ) -> None:
        """Initialize a client.

        Args:
            default_checks: Pre-built checks applied on every ``start_stream``
                call. Shallow-copied; **do not** mutate originals after passing.
            rts_cores: GHC RTS capabilities (default 1). Mismatch across
                clients logs a warning.
        """
        self._lib: ctypes.CDLL | None = None
        self._state: ctypes.c_void_p | None = None
        self._diags: dict[int, PropertyDiagnostic] = {}
        self._caches = StreamCaches()
        self._default_checks: list[CheckResult] = list(default_checks) if default_checks else []
        self._rts_cores: int = rts_cores
        # Per-message signal name/index lookup, populated by ``parse_dbc``.
        self._signal_lookup: dict[tuple[int, bool], SignalLookup] = {}

    def __enter__(self) -> Self:
        """Load shared library and initialize Haskell RTS."""
        lib_path = find_ffi_library()
        self._lib = ctypes.CDLL(str(lib_path))
        configure_ffi_signatures(self._lib)

        # Initialize GHC RTS (ref-counted, only first client actually calls hs_init)
        RTSState.acquire(self._lib, self._rts_cores)

        # Create Aletheia state
        raw = self._lib.aletheia_init()
        if not raw:
            raise ProcessError("aletheia_init() returned null — FFI initialization failed")
        self._state = ctypes.c_void_p(raw)

        return self

    def close(self) -> None:
        """Free state and release RTS reference."""
        try:
            if self._lib is not None and self._state is not None:
                self._lib.aletheia_close(self._state)
        finally:
            self._state = None
            if self._lib is not None:
                RTSState.release()
                self._lib = None

    def __exit__(
        self,
        exc_type: type[BaseException] | None,
        exc_val: BaseException | None,
        exc_tb: object,
    ) -> None:
        self.close()

    def _send_command(self, command: Command) -> Response:
        """Send command via FFI."""
        if self._lib is None or self._state is None:
            raise ProcessError("Client not initialized — use 'with' statement")

        json_bytes = dump_json(command).encode("utf-8")
        result_ptr = self._lib.aletheia_process(self._state, json_bytes)

        try:
            result_bytes = ctypes.cast(result_ptr, ctypes.c_char_p).value
            if result_bytes is None:
                raise ProtocolError("FFI returned null pointer")
            result_str = result_bytes.decode("utf-8")
        finally:
            self._lib.aletheia_free_str(result_ptr)

        return cast(Response, parse_json_object(result_str))

    def _parse_ffi_result(self, result_ptr: int) -> Response:
        """Decode JSON response from a binary FFI call and free the C string."""
        if self._lib is None:
            raise ProcessError("Client not initialized — use 'with' statement")
        try:
            result_bytes = ctypes.cast(result_ptr, ctypes.c_char_p).value
            if result_bytes is None:
                raise ProtocolError("FFI returned null pointer")
            result_str = result_bytes.decode("utf-8")
        finally:
            self._lib.aletheia_free_str(result_ptr)
        return cast(Response, parse_json_object(result_str))

    def _resolve_signal_indices(
        self, signals: Mapping[str, float | Fraction],
        can_id: int, extended: bool, cmd_name: str,
    ) -> SignalValues:
        """Resolve signal names to indices and convert values to rationals.

        Accepts float or Fraction inputs — Fraction flows through losslessly
        via ``coerce_to_rational``, matching the Agda core's ℚ arithmetic.
        """
        lookup = self._signal_lookup.get((can_id, extended))
        if lookup is None:
            if not self._signal_lookup:
                raise ProcessError(f"{cmd_name}: DBC not loaded (call parse_dbc first)")
            raise ProcessError(f"{cmd_name}: no DBC message for CAN ID {can_id}")
        indices: list[int] = []
        nums: list[int] = []
        dens: list[int] = []
        for name, value in signals.items():
            idx = lookup.indices.get(name)
            if idx is None:
                raise ProcessError(f"{cmd_name}: unknown signal '{name}'")
            n, d = coerce_to_rational(value)
            indices.append(idx)
            nums.append(n)
            dens.append(d)
        return SignalValues(
            indices=tuple(indices), numerators=tuple(nums), denominators=tuple(dens),
        )

    def _populate_signal_lookup(self, dbc: DBCDefinition) -> None:
        """Refresh the per-message signal name/index cache from a DBC body."""
        self._signal_lookup.clear()
        for msg in dbc["messages"]:
            msg_ext = bool(msg.get("extended", False))
            sig_map: dict[str, int] = {}
            names: list[str] = []
            for i, sig in enumerate(msg["signals"]):
                sig_map[sig["name"]] = i
                names.append(sig["name"])
            key = (msg["id"], msg_ext)
            self._signal_lookup[key] = SignalLookup(names=tuple(names), indices=sig_map)

    # =========================================================================
    # DBC and Properties
    # =========================================================================

    def _finalize_parsed_dbc(
        self, result: ParsedDBCResponse | ErrorResponse,
    ) -> ParsedDBCResponse | ErrorResponse:
        """Log + populate the signal-name cache when the parse succeeded."""
        if result["status"] == "success":
            log_event(
                _logger, logging.INFO, LogEvent.DBC_PARSED,
                messages=len(result["dbc"]["messages"]),
            )
            self._populate_signal_lookup(result["dbc"])
        return result

    def parse_dbc(self, dbc: DBCDefinition) -> ParsedDBCResponse | ErrorResponse:
        """Parse and validate a DBC definition. Must be called first.

        Returns the canonical parsed body plus any non-error issues
        (warnings); validation errors short-circuit to ``ErrorResponse``.
        """
        cmd: ParseDBCCommand = {"type": "command", "command": "parseDBC", "dbc": dbc}
        return self._finalize_parsed_dbc(parse_parsed_dbc_response(self._send_command(cmd)))

    def parse_dbc_text(self, text: str) -> ParsedDBCResponse | ErrorResponse:
        """Parse and validate a DBC from raw .dbc file text via the Agda text parser.

        Mirrors :meth:`parse_dbc`'s response shape — no cantools dependency.
        """
        cmd: ParseDBCTextCommand = {"type": "command", "command": "parseDBCText", "text": text}
        return self._finalize_parsed_dbc(parse_parsed_dbc_response(self._send_command(cmd)))

    def validate_dbc(self, dbc: DBCDefinition) -> ValidationResponse:
        """Run structural validation on a DBC definition.

        Returns all issues found (not just the first). Does not modify
        client state — this is a read-only check.

        Args:
            dbc: DBC structure (use dbc_converter.dbc_to_json())

        Returns:
            ValidationResponse with status, has_errors, and issues list
        """
        cmd: ValidateDBCCommand = {
            "type": "command",
            "command": "validateDBC",
            "dbc": dbc
        }
        response = self._send_command(cmd)
        status = response.get("status")

        if status == "validation":
            vresp = cast(ValidationResponse, response)
            return {
                "status": "validation",
                "has_errors": vresp["has_errors"],
                "issues": validate_issue_severities(list(vresp["issues"])),
            }

        if status == "error":
            message = response.get("message", "Unknown error")
            raise ProtocolError(f"validateDBC failed: {message}")

        raise ProtocolError(
            f"Unexpected response status: {status!r} (expected 'validation' or 'error')"
        )

    def format_dbc(self) -> DBCDefinition:
        """Export the currently-loaded DBC as a JSON dict.

        The DBC must have been loaded via ``parse_dbc()`` first.
        Numeric fields are normalized to ``Fraction`` so the result
        preserves the Agda core's exact rational precision end-to-end.

        Returns:
            DBC definition dict matching the ``DBCDefinition`` schema.

        Raises:
            ProtocolError: If no DBC is loaded or response is unexpected.
        """
        if self._lib is None or self._state is None:
            raise ProcessError("Client not initialized — use 'with' statement")
        response = self._parse_ffi_result(
            self._lib.aletheia_format_dbc(self._state),
        )
        status = response.get("status")

        if status == "success":
            dbc = response.get("dbc")
            if not is_str_dict(dbc):
                raise ProtocolError("Expected 'dbc' field in formatDBC response")
            return normalize_dbc(dbc)

        if status == "error":
            message = response.get("message", "Unknown error")
            raise ProtocolError(f"formatDBC failed: {message}")

        raise ProtocolError(
            f"Unexpected response status: {status!r} (expected 'success' or 'error')"
        )

    def set_properties(self, properties: list[LTLFormula]) -> SuccessResponse | ErrorResponse:
        """Set LTL properties to check. Must be called before start_stream().

        Automatically derives diagnostics (formula description, referenced
        signals) from each formula for violation enrichment.

        Args:
            properties: List of LTL formulas (from DSL .to_dict())

        Returns:
            SuccessResponse or ErrorResponse
        """
        cmd: SetPropertiesCommand = {
            "type": "command",
            "command": "setProperties",
            "properties": properties
        }
        response = parse_success_or_error(self._send_command(cmd))
        if response["status"] == "success":
            self._diags.clear()
            self._caches.clear()
            for i, formula in enumerate(properties):
                self._diags[i] = build_diagnostic(formula)
            log_event(
                _logger, logging.INFO, LogEvent.PROPERTIES_SET,
                count=len(properties),
            )
        return response

    def add_checks(
        self, checks: list[CheckResult],
    ) -> SuccessResponse | ErrorResponse:
        """Set LTL checks, merging with registered default checks.

        Combines ``default_checks`` (from constructor) with *checks*,
        calls ``set_properties()`` atomically. Diagnostics are auto-derived
        from the formula structure.

        Args:
            checks: Session-specific checks to add after defaults.

        Returns:
            SuccessResponse or ErrorResponse from ``set_properties()``.
        """
        all_checks = self._default_checks + checks
        return self.set_properties([c.to_dict() for c in all_checks])

    # =========================================================================
    # Streaming LTL Checking
    # =========================================================================

    def start_stream(self) -> SuccessResponse | ErrorResponse:
        """Start streaming mode for incremental LTL checking.

        Returns:
            SuccessResponse or ErrorResponse
        """
        if self._lib is None or self._state is None:
            raise ProcessError("Client not initialized — use 'with' statement")
        response = parse_success_or_error(
            self._parse_ffi_result(self._lib.aletheia_start_stream(self._state)),
        )
        if response["status"] == "success":
            self._caches.clear()
            log_event(_logger, logging.INFO, LogEvent.STREAM_STARTED)
        return response

    def _enrich_violation(
        self,
        result: PropertyViolationResponse,
        frame_id: FrameIdentity,
        data: bytes | bytearray,
    ) -> None:
        """Enrich a violation response with signal diagnostics (in-place)."""
        if not self._diags:
            return
        idx = _rational_index(result["property_index"], "violation")
        diag = self._diags.get(idx)
        if diag is None:
            log_event(
                _logger, logging.WARNING, LogEvent.ENRICHMENT_PROPERTY_INDEX_OOB,
                index=idx, count=len(self._diags),
            )
            return

        # Extract signal values (cached, bounded).
        cache_key = (frame_id.can_id, frame_id.extended, bytes(data))
        extraction: SignalExtractionResult | None = self._caches.extraction.get(cache_key)
        if extraction is None:
            log_event(
                _logger, logging.DEBUG, LogEvent.CACHE_MISS,
                canId=frame_id.can_id, dlc=frame_id.dlc,
            )
            try:
                extraction = self.extract_signals(
                    can_id=frame_id.can_id, dlc=frame_id.dlc, data=data,
                    extended=frame_id.extended,
                )
                if len(self._caches.extraction) < MAX_EXTRACT_CACHE:
                    self._caches.extraction[cache_key] = extraction
                else:
                    log_event(
                        _logger, logging.WARNING, LogEvent.CACHE_FULL,
                        size=len(self._caches.extraction),
                    )
            except (AletheiaError, ValueError) as exc:
                # Enrichment is best-effort — the frame still streamed and the
                # core verdict is authoritative.  Emit a single-line warning
                # with the exception message; dropping ``exc_info`` keeps
                # production logs scannable (traceback-worthy paths use
                # ``_logger.error(..., exc_info=True)`` instead).
                log_event(
                    _logger, logging.WARNING, LogEvent.ENRICHMENT_EXTRACTION_FAILED,
                    canId=frame_id.can_id, error=str(exc),
                )
        else:
            log_event(
                _logger, logging.DEBUG, LogEvent.CACHE_HIT,
                canId=frame_id.can_id, dlc=frame_id.dlc,
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

    # Pre-encoded ack response bytes for fast-path comparison.
    # _ACK_BYTES is the compact form produced by the binary FFI path;
    # _ACK_BYTES_SPACED is the form from the JSON FFI path (json.dumps
    # adds a space after the colon).  Both are checked so that the hot
    # path avoids a full JSON parse regardless of which FFI path emitted
    # the response.
    _ACK_BYTES = b'{"status":"ack"}'
    _ACK_BYTES_SPACED = b'{"status": "ack"}'

    def send_frame(  # pylint: disable=too-many-arguments
        self,
        timestamp: int,
        can_id: int,
        dlc: int,
        data: bytes | bytearray,
        *,
        extended: bool = False,
    ) -> AckResponse | PropertyViolationResponse | ErrorResponse:
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

        Returns:
            AckResponse, PropertyViolationResponse, or ErrorResponse
        """
        if self._lib is None or self._state is None:
            raise ProcessError("Client not initialized — use 'with' statement")
        if timestamp < 0:
            raise ValueError("timestamp must be non-negative")
        validate_can_id(can_id, extended=extended)
        expected_bytes = dlc_to_bytes(dlc)  # validates dlc is in [0, 15]
        if len(data) != expected_bytes:
            raise ProcessError(
                f"payload length {len(data)} does not match DLC {dlc}"
                + f" (expected {expected_bytes} bytes)"
            )

        # Binary FFI: pass frame components directly (no JSON serialization)
        data_array = (ctypes.c_uint8 * len(data))(*data)
        result_ptr = self._lib.aletheia_send_frame(
            self._state,
            ctypes.c_uint64(timestamp),
            ctypes.c_uint32(can_id),
            ctypes.c_uint8(1 if extended else 0),
            ctypes.c_uint8(dlc),
            data_array,
            ctypes.c_uint8(len(data)),
        )
        try:
            result_bytes = ctypes.cast(result_ptr, ctypes.c_char_p).value
            if result_bytes is None:
                raise ProtocolError("FFI returned null pointer")

            # Track last frame per CAN ID for EOS enrichment.
            if self._diags:
                self._caches.last_frames[(can_id, extended)] = (dlc, bytearray(data))

            # Fast path: ack response (overwhelmingly common in streaming)
            if result_bytes in (self._ACK_BYTES, self._ACK_BYTES_SPACED):
                log_event(
                    _logger, logging.DEBUG, LogEvent.FRAME_PROCESSED,
                    ts=timestamp, canId=can_id, extended=extended,
                    response="ack",
                )
                return {"status": "ack"}

            # Slow path: violations/errors — full JSON parse
            result_str = result_bytes.decode("utf-8")
        finally:
            self._lib.aletheia_free_str(result_ptr)

        response = cast(Response, parse_json_object(result_str))
        result = parse_frame_response(response)

        if result["status"] == "fails":
            self._enrich_violation(
                result, FrameIdentity(can_id, extended, dlc), data,
            )
            log_event(
                _logger, logging.DEBUG, LogEvent.FRAME_PROCESSED,
                ts=timestamp, canId=can_id, extended=extended,
                response="violation",
            )
        else:
            log_event(
                _logger, logging.DEBUG, LogEvent.FRAME_PROCESSED,
                ts=timestamp, canId=can_id, extended=extended,
                response=result.get("status", "unknown"),
            )

        return result

    def send_frames(
        self,
        frames: list[CANFrameTuple],
    ) -> list[AckResponse | PropertyViolationResponse]:
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
            List of AckResponse or PropertyViolationResponse (no ErrorResponse
            entries; those stop the batch and raise BatchError).

        Raises:
            BatchError: Wraps the underlying exception (or an ErrorResponse)
                and carries ``partial_results`` and ``frame_index``.
        """
        results: list[AckResponse | PropertyViolationResponse] = []
        for i, (ts, cid, dlc, d, ext) in enumerate(frames):
            try:
                resp = self.send_frame(ts, cid, dlc, d, extended=ext)
            except Exception as exc:
                raise BatchError(exc, results, frame_index=i) from exc
            if resp["status"] == "error":
                err = ProcessError(
                    f"error code={resp['code']}: {resp['message']}",
                    code=resp["code"],
                )
                # Partial results contain only successfully-processed frames;
                # the error response for frame `i` is surfaced via ``err`` and
                # ``frame_index`` on the BatchError rather than being mixed
                # into the partial results list, matching the Go/C++ bindings.
                raise BatchError(err, results, frame_index=i) from err
            results.append(resp)
        return results

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
        if self._lib is None or self._state is None:
            raise ProcessError("Client not initialized — use 'with' statement")
        if timestamp < 0:
            raise ValueError("timestamp must be non-negative")
        result_ptr = self._lib.aletheia_send_error(
            self._state, ctypes.c_uint64(timestamp),
        )
        try:
            result_bytes = ctypes.cast(result_ptr, ctypes.c_char_p).value
            if result_bytes is None:
                raise ProtocolError("FFI returned null pointer")
            if result_bytes in (self._ACK_BYTES, self._ACK_BYTES_SPACED):
                log_event(
                    _logger, logging.DEBUG, LogEvent.ERROR_EVENT_SENT,
                    ts=timestamp, response="ack",
                )
                return {"status": "ack"}
            result_str = result_bytes.decode("utf-8")
        finally:
            self._lib.aletheia_free_str(result_ptr)
        response = cast(Response, parse_json_object(result_str))
        return parse_event_response(response, "error_event", timestamp)

    def send_remote(
        self, timestamp: int, can_id: int, *, extended: bool = False,
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
        if self._lib is None or self._state is None:
            raise ProcessError("Client not initialized — use 'with' statement")
        if timestamp < 0:
            raise ValueError("timestamp must be non-negative")
        validate_can_id(can_id, extended=extended)
        result_ptr = self._lib.aletheia_send_remote(
            self._state,
            ctypes.c_uint64(timestamp),
            ctypes.c_uint32(can_id),
            ctypes.c_uint8(1 if extended else 0),
        )
        try:
            result_bytes = ctypes.cast(result_ptr, ctypes.c_char_p).value
            if result_bytes is None:
                raise ProtocolError("FFI returned null pointer")
            if result_bytes in (self._ACK_BYTES, self._ACK_BYTES_SPACED):
                log_event(
                    _logger, logging.DEBUG, LogEvent.REMOTE_EVENT_SENT,
                    ts=timestamp, canId=can_id, extended=extended,
                    response="ack",
                )
                return {"status": "ack"}
            result_str = result_bytes.decode("utf-8")
        finally:
            self._lib.aletheia_free_str(result_ptr)
        response = cast(Response, parse_json_object(result_str))
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
        if self._lib is None or self._state is None:
            raise ProcessError("Client not initialized — use 'with' statement")
        response = self._parse_ffi_result(
            self._lib.aletheia_end_stream(self._state),
        )
        status = response.get("status")

        if status == "complete":
            results = parse_finalization_results(
                response, self._enrich_finalization_result,
            )
            num_fails = sum(1 for r in results if r["status"] == "fails")
            num_unresolved = sum(1 for r in results if r["status"] == "unresolved")
            self._caches.last_frames.clear()
            log_event(
                _logger, logging.INFO, LogEvent.STREAM_ENDED,
                numResults=len(results), numFails=num_fails,
                numUnresolved=num_unresolved,
            )
            return {"status": "complete", "results": results}

        if status == "error":
            return build_error_response(response)

        raise ProtocolError(
            f"Unexpected response status: {status!r} (expected 'complete' or 'error')"
        )

    def _extract_last_known_values(
        self, diag: PropertyDiagnostic,
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
                    can_id=lf_id, dlc=lf_dlc, data=lf_data, extended=lf_ext,
                )
            except (AletheiaError, ValueError) as exc:
                # Finalization enrichment is best-effort (mirrors the hot
                # path); keep the warning single-line so operators can grep
                # ``enrichment.extraction_failed`` without drowning in
                # tracebacks.
                log_event(
                    _logger, logging.WARNING, LogEvent.ENRICHMENT_EXTRACTION_FAILED,
                    canId=lf_id, error=str(exc),
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
        self, result: PropertyResultEntry,
    ) -> None:
        """Enrich an end-of-stream violation with signal diagnostics."""
        if not self._diags:
            return
        idx = _rational_index(result["property_index"], "finalization")
        diag = self._diags.get(idx)
        if diag is None:
            log_event(
                _logger, logging.WARNING, LogEvent.ENRICHMENT_PROPERTY_INDEX_OOB,
                index=idx, count=len(self._diags),
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

    # =========================================================================
    # Signal Operations (available anytime after DBC loaded)
    # =========================================================================

    def extract_signals(
        self, can_id: int, dlc: int, data: bytes | bytearray,
        *, extended: bool = False,
    ) -> SignalExtractionResult:
        """Extract all signals from a CAN frame.

        Works both inside and outside streaming mode.

        Args:
            can_id: CAN message ID
            dlc: DLC code (0-8 for CAN 2.0B, 0-15 for CAN-FD)
            data: Frame payload
            extended: True for 29-bit extended CAN ID, False for 11-bit standard

        Returns:
            SignalExtractionResult with values/errors/absent partitioning

        Raises:
            ProcessError: If extraction fails
            ValueError: If dlc is outside 0-15
        """
        if self._lib is None or self._state is None:
            raise ProcessError("Client not initialized — use 'with' statement")
        expected_bytes = dlc_to_bytes(dlc)  # validates dlc is in [0, 15]
        if len(data) != expected_bytes:
            raise ProcessError(
                f"payload length {len(data)} does not match DLC {dlc}"
                + f" (expected {expected_bytes} bytes)"
            )
        validate_can_id(can_id, extended=extended)
        data_array = (ctypes.c_uint8 * len(data))(*data)

        # Use binary path when signal name cache is populated
        lookup = self._signal_lookup.get((can_id, extended))
        if lookup is not None:
            return BinaryFFI(self._lib, self._state).extract_signals(
                FrameIdentity(can_id, extended, dlc),
                data_array,
                lookup.names,
            )

        # Fallback: JSON path
        result_ptr = self._lib.aletheia_extract_signals(
            self._state,
            ctypes.c_uint32(can_id),
            ctypes.c_uint8(1 if extended else 0),
            ctypes.c_uint8(dlc),
            data_array,
            ctypes.c_uint8(len(data)),
        )
        try:
            response = self._parse_ffi_result(result_ptr)
        except (ProcessError, ProtocolError) as exc:
            log_event(
                _logger, logging.WARNING, LogEvent.EXTRACTION_PROCESS_FAILED,
                canId=can_id, error=str(exc),
            )
            raise

        if response.get("status") == "error":
            error_msg = response.get("message", "Unknown error")
            error_code_raw = response.get("code")
            error_code = error_code_raw if isinstance(error_code_raw, str) else None
            log_event(
                _logger, logging.WARNING, LogEvent.EXTRACTION_PARSE_FAILED,
                canId=can_id, error=error_msg,
            )
            # Forward the Agda wire ``code`` so callers can branch on e.g.
            # ``extraction_bit_extraction_failed`` vs ``frame_signal_not_found``
            # without parsing the message string (matches Go / C++ bindings).
            raise ProcessError(
                f"extract_signals failed: {error_msg}", code=error_code,
            )
        if response.get("status") != "success":
            raise ProtocolError(f"Unexpected status: {response.get('status')}")

        # Parse response — validate list types, then delegate to helpers
        for key in ("values", "errors", "absent"):
            if not is_object_list(response.get(key, [])):
                raise ProtocolError(f"Expected '{key}' to be a list")
        return SignalExtractionResult(
            values=parse_values_list(response.get("values", [])),
            errors=parse_errors_list(response.get("errors", [])),
            absent=tuple(parse_absent_list(response.get("absent", []))),
        )

    def update_frame(  # pylint: disable=too-many-arguments
        self,
        can_id: int,
        dlc: int,
        frame: bytes | bytearray,
        signals: Mapping[str, float | Fraction],
        *,
        extended: bool = False,
    ) -> bytearray:
        """Update specific signals in an existing frame.

        Works both inside and outside streaming mode.
        Immutable - returns new frame, original unchanged.

        Args:
            can_id: CAN message ID
            dlc: DLC code (0-8 for CAN 2.0B, 0-15 for CAN-FD)
            frame: Existing frame data
            signals: Signal updates (name -> value)
            extended: True for 29-bit extended CAN ID, False for 11-bit standard

        Returns:
            New frame with updated signals

        Raises:
            ProcessError: If update fails
            ValueError: If dlc is outside 0-15
        """
        if self._lib is None or self._state is None:
            raise ProcessError("Client not initialized — use 'with' statement")
        expected_bytes = dlc_to_bytes(dlc)
        if len(frame) != expected_bytes:
            raise ProcessError(
                f"payload length {len(frame)} does not match DLC {dlc}"
                + f" (expected {expected_bytes} bytes)"
            )
        validate_can_id(can_id, extended=extended)
        sig_values = self._resolve_signal_indices(
            signals, can_id, extended, "update_frame",
        )
        frame_array = (ctypes.c_uint8 * len(frame))(*frame)
        return BinaryFFI(self._lib, self._state).update_frame(
            FrameIdentity(can_id, extended, dlc),
            frame_array,
            sig_values,
            expected_bytes,
        )

    def build_frame(
        self, can_id: int, dlc: int, signals: Mapping[str, float | Fraction], *,
        extended: bool = False,
    ) -> bytearray:
        """Build a CAN frame from signal values (zero-filled base).

        Args:
            can_id: CAN message ID
            dlc: Data Length Code (0-15).
            signals: Signal values to encode (name -> value)
            extended: True for 29-bit extended CAN ID, False for 11-bit standard

        Returns:
            CAN frame payload (length = dlc_to_bytes(dlc))

        Raises:
            ProcessError: If frame building fails
            ValueError: If dlc is outside 0-15
        """
        if self._lib is None or self._state is None:
            raise ProcessError("Client not initialized — use 'with' statement")
        validate_can_id(can_id, extended=extended)
        sig_values = self._resolve_signal_indices(
            signals, can_id, extended, "build_frame",
        )
        return BinaryFFI(self._lib, self._state).build_frame(
            FrameIdentity(can_id, extended, dlc),
            sig_values,
            dlc_to_bytes(dlc),
        )

    @override
    def __repr__(self) -> str:
        return "AletheiaClient()"
