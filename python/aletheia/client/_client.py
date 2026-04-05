"""AletheiaClient — streaming LTL checking and signal operations via FFI."""

from __future__ import annotations

import ctypes
import json
import logging
import struct
from typing import TYPE_CHECKING, Self, override, cast

from ..protocols import (
    DBCDefinition,
    LTLFormula,
    Command,
    Response,
    ParseDBCCommand,
    SetPropertiesCommand,
    BuildFrameResponse,
    UpdateFrameResponse,
    ValidateDBCCommand,
    SuccessResponse,
    CompleteResponse,
    AckResponse,
    PropertyViolationResponse,
    PropertyResultEntry,
    ErrorResponse,
    ValidationIssue,
    ValidationResponse,
    is_str_dict,
    is_object_list,
)
from ._enrichment import build_diagnostic, format_enriched_reason
from ._ffi import parse_json_object, RTSState, find_ffi_library
from ._helpers import (
    float_to_rational,
    validate_rational,
    normalize_dbc,
    parse_frame_data,
    parse_values_list,
    parse_errors_list,
    parse_absent_list,
)
from ._types import (
    AletheiaError,
    BatchError,
    ProcessError,
    ProtocolError,
    SignalExtractionResult,
    PropertyDiagnostic,
    ExtractionCache,
    MAX_EXTRACT_CACHE,
    dlc_to_bytes,
    validate_can_id,
)

if TYPE_CHECKING:
    from ..checks import CheckResult

_logger = logging.getLogger("aletheia")


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
        self._lib: ctypes.CDLL | None = None
        self._state: ctypes.c_void_p | None = None
        self._diags: dict[int, PropertyDiagnostic] = {}
        self._signal_cache: ExtractionCache = {}
        self._default_checks: list[CheckResult] = list(default_checks) if default_checks else []
        self._rts_cores: int = rts_cores
        self._signal_index_cache: dict[tuple[int, bool], dict[str, int]] = {}
        self._signal_names_cache: dict[tuple[int, bool], list[str]] = {}
        self._last_timestamp: int | None = None

    def __enter__(self) -> Self:
        """Load shared library and initialize Haskell RTS."""
        lib_path = find_ffi_library()
        self._lib = ctypes.CDLL(str(lib_path))

        # Set up function signatures
        self._lib.aletheia_init.argtypes = []
        self._lib.aletheia_init.restype = ctypes.c_void_p
        self._lib.aletheia_process.argtypes = [ctypes.c_void_p, ctypes.c_char_p]
        self._lib.aletheia_process.restype = ctypes.c_void_p
        self._lib.aletheia_free_str.argtypes = [ctypes.c_void_p]
        self._lib.aletheia_free_str.restype = None
        self._lib.aletheia_close.argtypes = [ctypes.c_void_p]
        self._lib.aletheia_close.restype = None

        # Binary frame endpoint (hot path — bypasses JSON serialization on input)
        self._lib.aletheia_send_frame.argtypes = [
            ctypes.c_void_p,                 # state
            ctypes.c_uint64,                 # timestamp
            ctypes.c_uint32,                 # can_id
            ctypes.c_uint8,                  # extended (0 or 1)
            ctypes.c_uint8,                  # dlc
            ctypes.POINTER(ctypes.c_uint8),  # data pointer
            ctypes.c_uint8,                  # data_len
        ]
        self._lib.aletheia_send_frame.restype = ctypes.c_void_p

        # Binary entry points (no JSON parsing on input)
        self._lib.aletheia_start_stream.argtypes = [ctypes.c_void_p]
        self._lib.aletheia_start_stream.restype = ctypes.c_void_p
        self._lib.aletheia_end_stream.argtypes = [ctypes.c_void_p]
        self._lib.aletheia_end_stream.restype = ctypes.c_void_p
        self._lib.aletheia_format_dbc.argtypes = [ctypes.c_void_p]
        self._lib.aletheia_format_dbc.restype = ctypes.c_void_p
        self._lib.aletheia_extract_signals.argtypes = [
            ctypes.c_void_p,                 # state
            ctypes.c_uint32,                 # can_id
            ctypes.c_uint8,                  # extended
            ctypes.c_uint8,                  # dlc
            ctypes.POINTER(ctypes.c_uint8),  # data pointer
            ctypes.c_uint8,                  # data_len
        ]
        self._lib.aletheia_extract_signals.restype = ctypes.c_void_p
        self._lib.aletheia_build_frame.argtypes = [
            ctypes.c_void_p,                  # state
            ctypes.c_uint32,                  # can_id
            ctypes.c_uint8,                   # extended
            ctypes.c_uint8,                   # dlc
            ctypes.c_uint32,                  # numSignals
            ctypes.POINTER(ctypes.c_uint32),  # indices
            ctypes.POINTER(ctypes.c_int64),   # numerators
            ctypes.POINTER(ctypes.c_int64),   # denominators
        ]
        self._lib.aletheia_build_frame.restype = ctypes.c_void_p
        self._lib.aletheia_update_frame.argtypes = [
            ctypes.c_void_p,                  # state
            ctypes.c_uint32,                  # can_id
            ctypes.c_uint8,                   # extended
            ctypes.c_uint8,                   # dlc
            ctypes.POINTER(ctypes.c_uint8),   # data pointer
            ctypes.c_uint8,                   # data_len
            ctypes.c_uint32,                  # numSignals
            ctypes.POINTER(ctypes.c_uint32),  # indices
            ctypes.POINTER(ctypes.c_int64),   # numerators
            ctypes.POINTER(ctypes.c_int64),   # denominators
        ]
        self._lib.aletheia_update_frame.restype = ctypes.c_void_p

        # CAN error/remote event endpoints (acknowledged without LTL evaluation)
        self._lib.aletheia_send_error.argtypes = [
            ctypes.c_void_p,   # state
            ctypes.c_uint64,   # timestamp
        ]
        self._lib.aletheia_send_error.restype = ctypes.c_void_p
        self._lib.aletheia_send_remote.argtypes = [
            ctypes.c_void_p,   # state
            ctypes.c_uint64,   # timestamp
            ctypes.c_uint32,   # can_id
            ctypes.c_uint8,    # extended (0 or 1)
        ]
        self._lib.aletheia_send_remote.restype = ctypes.c_void_p

        # Binary output entry points (no JSON on output either)
        self._lib.aletheia_build_frame_bin.argtypes = [
            ctypes.c_void_p,                  # state
            ctypes.c_uint32,                  # can_id
            ctypes.c_uint8,                   # extended
            ctypes.c_uint8,                   # dlc
            ctypes.c_uint32,                  # numSignals
            ctypes.POINTER(ctypes.c_uint32),  # indices
            ctypes.POINTER(ctypes.c_int64),   # numerators
            ctypes.POINTER(ctypes.c_int64),   # denominators
            ctypes.POINTER(ctypes.c_uint8),   # out_buf
            ctypes.POINTER(ctypes.c_char_p),  # out_err
        ]
        self._lib.aletheia_build_frame_bin.restype = ctypes.c_int8
        self._lib.aletheia_update_frame_bin.argtypes = [
            ctypes.c_void_p,                  # state
            ctypes.c_uint32,                  # can_id
            ctypes.c_uint8,                   # extended
            ctypes.c_uint8,                   # dlc
            ctypes.POINTER(ctypes.c_uint8),   # data pointer
            ctypes.c_uint8,                   # data_len
            ctypes.c_uint32,                  # numSignals
            ctypes.POINTER(ctypes.c_uint32),  # indices
            ctypes.POINTER(ctypes.c_int64),   # numerators
            ctypes.POINTER(ctypes.c_int64),   # denominators
            ctypes.POINTER(ctypes.c_uint8),   # out_buf
            ctypes.POINTER(ctypes.c_char_p),  # out_err
        ]
        self._lib.aletheia_update_frame_bin.restype = ctypes.c_int8
        self._lib.aletheia_extract_signals_bin.argtypes = [
            ctypes.c_void_p,                          # state
            ctypes.c_uint32,                           # can_id
            ctypes.c_uint8,                            # extended
            ctypes.c_uint8,                            # dlc
            ctypes.POINTER(ctypes.c_uint8),            # data pointer
            ctypes.c_uint8,                            # data_len
            ctypes.POINTER(ctypes.POINTER(ctypes.c_uint8)),  # out_buf
            ctypes.POINTER(ctypes.c_uint32),           # out_size
            ctypes.POINTER(ctypes.c_char_p),           # out_err
        ]
        self._lib.aletheia_extract_signals_bin.restype = ctypes.c_int8
        self._lib.aletheia_free_buf.argtypes = [ctypes.POINTER(ctypes.c_uint8)]
        self._lib.aletheia_free_buf.restype = None

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

        json_bytes = json.dumps(command).encode("utf-8")
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
        assert self._lib is not None
        try:
            result_bytes = ctypes.cast(result_ptr, ctypes.c_char_p).value
            if result_bytes is None:
                raise ProtocolError("FFI returned null pointer")
            result_str = result_bytes.decode("utf-8")
        finally:
            self._lib.aletheia_free_str(result_ptr)
        return cast(Response, parse_json_object(result_str))

    def _resolve_signal_indices(
        self, signals: dict[str, float], can_id: int, extended: bool, cmd_name: str,
    ) -> tuple[list[int], list[int], list[int]]:
        """Resolve signal names to indices and convert values to rationals.

        Returns (indices, numerators, denominators) as parallel lists.
        """
        index_map = self._signal_index_cache.get((can_id, extended))
        if index_map is None:
            if not self._signal_index_cache:
                raise ProcessError(f"{cmd_name}: DBC not loaded")
            raise ProcessError(f"{cmd_name}: no DBC message for CAN ID {can_id}")
        indices: list[int] = []
        nums: list[int] = []
        dens: list[int] = []
        for name, value in signals.items():
            idx = index_map.get(name)
            if idx is None:
                raise ProcessError(f"{cmd_name}: unknown signal '{name}'")
            n, d = float_to_rational(value)
            indices.append(idx)
            nums.append(n)
            dens.append(d)
        return indices, nums, dens

    def _success_or_error(self, response: Response) -> SuccessResponse | ErrorResponse:
        """Parse a response that should be success or error."""
        status = response.get("status")
        message = response.get("message")

        if status == "success":
            result: SuccessResponse = {"status": "success"}
            if isinstance(message, str):
                result["message"] = message
            return result

        if status == "error":
            err: ErrorResponse = {"status": "error", "message": ""}
            if isinstance(message, str):
                err["message"] = message
            return err

        raise ProtocolError(
            f"Unexpected response status: {status!r} (expected 'success' or 'error')"
        )

    # =========================================================================
    # DBC and Properties
    # =========================================================================

    def parse_dbc(self, dbc: DBCDefinition) -> SuccessResponse | ErrorResponse:
        """Parse DBC file. Must be called first.

        Args:
            dbc: DBC structure (use dbc_converter.dbc_to_json())

        Returns:
            SuccessResponse or ErrorResponse
        """
        cmd: ParseDBCCommand = {
            "type": "command",
            "command": "parseDBC",
            "dbc": dbc
        }
        result = self._success_or_error(self._send_command(cmd))
        if result["status"] == "success":
            self._signal_index_cache.clear()
            self._signal_names_cache.clear()
            for msg in dbc["messages"]:
                msg_ext = bool(msg.get("extended", False))
                sig_map: dict[str, int] = {}
                names: list[str] = []
                for i, sig in enumerate(msg["signals"]):
                    sig_map[sig["name"]] = i
                    names.append(sig["name"])
                key = (msg["id"], msg_ext)
                self._signal_index_cache[key] = sig_map
                self._signal_names_cache[key] = names
        return result

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
            issues: list[ValidationIssue] = list(vresp["issues"])
            return {
                "status": "validation",
                "has_errors": vresp["has_errors"],
                "issues": issues,
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
        Numeric fields are normalized to ``float`` so the result
        matches the ``DBCDefinition`` schema exactly.

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
        response = self._success_or_error(self._send_command(cmd))
        if response["status"] == "success":
            self._diags.clear()
            self._signal_cache.clear()
            for i, formula in enumerate(properties):
                self._diags[i] = build_diagnostic(formula)
            _logger.info("properties.set count=%d", len(properties))
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
        self._signal_cache.clear()
        response = self._success_or_error(
            self._parse_ffi_result(self._lib.aletheia_start_stream(self._state)),
        )
        if response["status"] == "success":
            _logger.info("stream.started")
        return response

    def _enrich_violation(
        self,
        result: PropertyViolationResponse,
        can_id: int,
        dlc: int,
        data: bytearray,
    ) -> None:
        """Enrich a violation response with signal diagnostics (in-place)."""
        if not self._diags:
            return
        prop_index_r = result["property_index"]
        idx = prop_index_r["numerator"] // prop_index_r["denominator"]
        diag = self._diags.get(idx)
        if diag is None:
            _logger.warning(
                "enrichment.property_index_oob index=%d count=%d",
                idx, len(self._diags),
            )
            return

        # Extract signal values (cached, bounded).
        cache_key: tuple[int, bytes] = (can_id, bytes(data))
        extraction: SignalExtractionResult | None = self._signal_cache.get(cache_key)
        if extraction is None:
            _logger.debug("cache.miss canId=%d dlc=%d", can_id, dlc)
            try:
                extraction = self.extract_signals(can_id=can_id, dlc=dlc, data=data)
                if len(self._signal_cache) < MAX_EXTRACT_CACHE:
                    self._signal_cache[cache_key] = extraction
                else:
                    _logger.warning(
                        "cache.full size=%d", len(self._signal_cache),
                    )
            except (AletheiaError, ValueError) as exc:
                _logger.warning(
                    "enrichment.extraction_failed canId=%d error=%s",
                    can_id, exc,
                )
        else:
            _logger.debug("cache.hit canId=%d dlc=%d", can_id, dlc)

        values: dict[str, float | None] = {}
        if extraction is not None:
            for sig in diag.signals:
                val = extraction.values.get(sig)
                if val is not None:
                    values[sig] = val

        result["signals"] = values
        result["formula"] = diag.formula_desc
        result["enriched_reason"] = format_enriched_reason(diag, values)

    # Pre-encoded ack response bytes for fast-path comparison
    _ACK_BYTES = b'{"status":"ack"}'
    _ACK_BYTES_SPACED = b'{"status": "ack"}'

    def send_frame(  # pylint: disable=too-many-arguments
        self,
        timestamp: int,
        can_id: int,
        dlc: int,
        data: bytearray,
        *,
        extended: bool = False,
    ) -> AckResponse | PropertyViolationResponse | ErrorResponse:
        """Send a CAN frame for incremental LTL checking.

        If properties have been set via ``set_properties()``, violation
        responses are automatically enriched with ``signals``, ``formula``,
        and ``enriched_reason``.

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
        if self._last_timestamp is not None and timestamp < self._last_timestamp:
            raise ValueError(
                f"non-monotonic timestamp: {timestamp} µs < previous {self._last_timestamp} µs"
                " (metric LTL operators require monotonic timestamps)"
            )
        self._last_timestamp = timestamp
        validate_can_id(can_id, extended=extended)
        dlc_to_bytes(dlc)  # validates dlc is in [0, 15]

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

            # Fast path: ack response (overwhelmingly common in streaming)
            if result_bytes in (self._ACK_BYTES, self._ACK_BYTES_SPACED):
                _logger.debug(
                    "frame.processed ts=%d canId=%d extended=%s response=ack",
                    timestamp, can_id, extended,
                )
                return {"status": "ack"}

            # Slow path: violations/errors — full JSON parse
            result_str = result_bytes.decode("utf-8")
        finally:
            self._lib.aletheia_free_str(result_ptr)

        response = cast(Response, parse_json_object(result_str))
        result = self._parse_frame_response(response)

        if result["status"] == "fails":
            self._enrich_violation(result, can_id, dlc, data)
            _logger.debug(
                "frame.processed ts=%d canId=%d extended=%s response=violation",
                timestamp, can_id, extended,
            )
        else:
            _logger.debug(
                "frame.processed ts=%d canId=%d extended=%s response=%s",
                timestamp, can_id, extended, result.get("status", "unknown"),
            )

        return result

    def _parse_frame_response(
        self, response: Response,
    ) -> AckResponse | PropertyViolationResponse | ErrorResponse:
        """Parse a single frame response into a typed result."""
        status = response.get("status")

        if status == "ack":
            return {"status": "ack"}

        if status == "fails":
            prop_type = response.get("type")
            if prop_type != "property":
                raise ProtocolError(f"Expected type='property', got {prop_type}")
            prop_index = validate_rational("property_index", response.get("property_index"))
            ts_rational = validate_rational("timestamp", response.get("timestamp"))
            result_violation: PropertyViolationResponse = {
                "status": "fails",
                "type": "property",
                "property_index": prop_index,
                "timestamp": ts_rational,
            }
            reason = response.get("reason")
            if isinstance(reason, str):
                result_violation["reason"] = reason
            return result_violation

        if status == "error":
            result_error: ErrorResponse = {"status": "error", "message": ""}
            message = response.get("message")
            if isinstance(message, str):
                result_error["message"] = message
            return result_error

        raise ProtocolError(
            f"Unexpected response status: {status!r} (expected 'ack', 'fails', or 'error')"
        )

    def send_frames_batch(
        self,
        frames: list[tuple[int, int, int, bytearray]],
        *,
        extended: bool = False,
    ) -> list[AckResponse | PropertyViolationResponse | ErrorResponse]:
        """Send multiple CAN frames in a batch.

        A violation is a normal response and does not stop the batch.
        Processing stops at the first transport or validation error. Partial
        results from frames processed before the error are returned via
        the ``partial_results`` attribute on the raised ``BatchError``.

        Args:
            frames: List of (timestamp, can_id, dlc, data) tuples where:
                - timestamp: Timestamp in microseconds
                - can_id: CAN ID (11-bit standard or 29-bit extended)
                - dlc: DLC code (0-8 for CAN 2.0B, 0-15 for CAN-FD)
                - data: Frame payload
            extended: True for 29-bit extended CAN IDs, False for 11-bit standard

        Returns:
            List of responses in same order as input frames.

        Raises:
            BatchError: Wraps the underlying exception and carries
                ``partial_results`` with responses collected before the error.
        """
        results: list[AckResponse | PropertyViolationResponse | ErrorResponse] = []
        for ts, cid, dlc, d in frames:
            try:
                results.append(self.send_frame(ts, cid, dlc, d, extended=extended))
            except Exception as exc:
                raise BatchError(exc, results) from exc
        return results

    def send_error(self, timestamp: int) -> AckResponse:
        """Send a CAN error event (no ID, no payload).

        Error frames signal a bus error detected by a CAN controller.
        They are acknowledged without LTL evaluation — error frames carry
        no payload for signal extraction.

        Args:
            timestamp: Timestamp in microseconds
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
        finally:
            self._lib.aletheia_free_str(result_ptr)
        _logger.debug("error_event.sent ts=%d", timestamp)
        return {"status": "ack"}

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
        finally:
            self._lib.aletheia_free_str(result_ptr)
        _logger.debug("remote_event.sent ts=%d canId=%d extended=%s", timestamp, can_id, extended)
        return {"status": "ack"}

    def end_stream(self) -> CompleteResponse | ErrorResponse:
        """End streaming mode and finalize all properties.

        Returns:
            CompleteResponse with per-property finalization results, or
            ErrorResponse if not currently streaming.

        The ``results`` list contains one entry per property:
        - ``status="holds"`` if the property held on the finite trace
        - ``status="fails"`` if the property failed at end-of-stream
          (e.g., safety property never resolved, liveness never satisfied)

        Violations are enriched with ``signals``, ``formula``, and
        ``enriched_reason`` when checks have been registered.
        """
        if self._lib is None or self._state is None:
            raise ProcessError("Client not initialized — use 'with' statement")
        response = self._parse_ffi_result(
            self._lib.aletheia_end_stream(self._state),
        )
        status = response.get("status")
        message = response.get("message")

        if status == "complete":
            results = self._parse_finalization_results(response)
            num_fails = sum(1 for r in results if r["status"] == "fails")
            _logger.info(
                "stream.ended numResults=%d numFails=%d",
                len(results), num_fails,
            )
            return {"status": "complete", "results": results}

        if status == "error":
            result_error: ErrorResponse = {"status": "error", "message": ""}
            if isinstance(message, str):
                result_error["message"] = message
            return result_error

        raise ProtocolError(
            f"Unexpected response status: {status!r} (expected 'complete' or 'error')"
        )

    def _parse_finalization_results(
        self, response: Response,
    ) -> list[PropertyResultEntry]:
        """Parse end-of-stream property finalization results."""
        cresp = cast(CompleteResponse, response)
        raw_results = cresp["results"]
        entries: list[PropertyResultEntry] = []
        for raw in raw_results:
            entry_status = raw["status"]
            prop_index = validate_rational(
                "property_index", raw["property_index"],
            )
            result_entry: PropertyResultEntry = {
                "type": "property",
                "status": entry_status,
                "property_index": prop_index,
            }
            if entry_status == "fails":
                ts = raw.get("timestamp")
                if ts is not None:
                    result_entry["timestamp"] = validate_rational(
                        "timestamp", ts,
                    )
                reason = raw.get("reason")
                if isinstance(reason, str):
                    result_entry["reason"] = reason
                self._enrich_finalization_result(result_entry)
            entries.append(result_entry)
        return entries

    def _enrich_finalization_result(
        self, result: PropertyResultEntry,
    ) -> None:
        """Enrich an end-of-stream violation with signal diagnostics."""
        if not self._diags:
            return
        prop_index_r = result["property_index"]
        idx = prop_index_r["numerator"] // prop_index_r["denominator"]
        diag = self._diags.get(idx)
        if diag is None:
            _logger.warning(
                "enrichment.property_index_oob index=%d count=%d",
                idx, len(self._diags),
            )
            return
        result["formula"] = diag.formula_desc
        result["enriched_reason"] = "violated: " + diag.formula_desc

    # =========================================================================
    # Signal Operations (available anytime after DBC loaded)
    # =========================================================================

    def extract_signals(
        self, can_id: int, dlc: int, data: bytearray,
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
                "ExtractAllSignals: byte count doesn't match DLC: "
                + f"expected {expected_bytes}, got {len(data)}"
            )
        validate_can_id(can_id, extended=extended)
        data_array = (ctypes.c_uint8 * len(data))(*data)

        # Use binary path when signal name cache is populated
        names = self._signal_names_cache.get((can_id, extended))
        if names is not None:
            return self._extract_signals_bin(
                can_id, extended, dlc, data_array, len(data), names,
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
        response = self._parse_ffi_result(result_ptr)

        if response.get("status") == "error":
            error_msg = response.get("message", "Unknown error")
            raise ProcessError(f"Extract signals failed: {error_msg}")
        if response.get("status") != "success":
            raise ProtocolError(f"Unexpected status: {response.get('status')}")

        # Parse response — validate list types, then delegate to helpers
        for key in ("values", "errors", "absent"):
            if not is_object_list(response.get(key, [])):
                raise ProtocolError(f"Expected '{key}' to be a list")
        return SignalExtractionResult(
            values=parse_values_list(response.get("values", [])),
            errors=parse_errors_list(response.get("errors", [])),
            absent=parse_absent_list(response.get("absent", [])),
        )

    # Error code → message mapping for binary extraction
    _EXTRACTION_ERROR_MESSAGES: tuple[str, ...] = (
        "Signal not found in DBC",     # 0
        "Value out of bounds",          # 1
        "Extraction failed",            # 2
    )

    def _extract_signals_bin(
        self,
        can_id: int,
        extended: bool,
        dlc: int,
        data_array: ctypes.Array[ctypes.c_uint8],
        data_len: int,
        names: list[str],
    ) -> SignalExtractionResult:
        """Binary extraction path — no JSON on input or output."""
        out_buf = ctypes.POINTER(ctypes.c_uint8)()
        out_size = ctypes.c_uint32()
        out_err = ctypes.c_char_p()
        status = self._lib.aletheia_extract_signals_bin(
            self._state,
            ctypes.c_uint32(can_id),
            ctypes.c_uint8(1 if extended else 0),
            ctypes.c_uint8(dlc),
            data_array,
            ctypes.c_uint8(data_len),
            ctypes.byref(out_buf),
            ctypes.byref(out_size),
            ctypes.byref(out_err),
        )
        if status != 0:
            err_msg = out_err.value.decode("utf-8") if out_err.value else "Unknown error"
            if out_err.value:
                self._lib.aletheia_free_str(out_err)
            raise ProcessError(f"Extract signals failed: {err_msg}")

        buf = bytes(ctypes.cast(out_buf, ctypes.POINTER(ctypes.c_uint8 * out_size.value)).contents)
        self._lib.aletheia_free_buf(out_buf)

        # Parse packed binary: header(6) + values(18 each) + errors(3 each) + absent(2 each)
        nvals, nerrs, nabss = struct.unpack_from("<HHH", buf, 0)
        off = 6
        values: dict[str, float] = {}
        for _ in range(nvals):
            idx, num, den = struct.unpack_from("<Hqq", buf, off)
            off += 18
            name = names[idx] if idx < len(names) else f"signal_{idx}"
            values[name] = num / den if den != 0 else 0.0

        errors: dict[str, str] = {}
        for _ in range(nerrs):
            idx, code = struct.unpack_from("<HB", buf, off)
            off += 3
            name = names[idx] if idx < len(names) else f"signal_{idx}"
            if code < len(self._EXTRACTION_ERROR_MESSAGES):
                errors[name] = self._EXTRACTION_ERROR_MESSAGES[code]
            else:
                errors[name] = f"Unknown error code {code}"

        absent: list[str] = []
        for _ in range(nabss):
            (idx,) = struct.unpack_from("<H", buf, off)
            off += 2
            name = names[idx] if idx < len(names) else f"signal_{idx}"
            absent.append(name)

        return SignalExtractionResult(values=values, errors=errors, absent=absent)

    def update_frame(  # pylint: disable=too-many-arguments
        self,
        can_id: int,
        dlc: int,
        frame: bytearray,
        signals: dict[str, float],
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
                "UpdateFrame: byte count doesn't match DLC: "
                + f"expected {expected_bytes}, got {len(frame)}"
            )
        validate_can_id(can_id, extended=extended)
        indices, nums, dens = self._resolve_signal_indices(
            signals, can_id, extended, "UpdateFrame",
        )
        n_signals = len(indices)
        frame_array = (ctypes.c_uint8 * len(frame))(*frame)
        out_buf = (ctypes.c_uint8 * expected_bytes)()
        out_err = ctypes.c_char_p()
        status = self._lib.aletheia_update_frame_bin(
            self._state,
            ctypes.c_uint32(can_id),
            ctypes.c_uint8(1 if extended else 0),
            ctypes.c_uint8(dlc),
            frame_array,
            ctypes.c_uint8(len(frame)),
            ctypes.c_uint32(n_signals),
            (ctypes.c_uint32 * n_signals)(*indices),
            (ctypes.c_int64 * n_signals)(*nums),
            (ctypes.c_int64 * n_signals)(*dens),
            out_buf,
            ctypes.byref(out_err),
        )
        if status != 0:
            err_msg = out_err.value.decode("utf-8") if out_err.value else "Unknown error"
            if out_err.value:
                self._lib.aletheia_free_str(out_err)
            raise ProcessError(f"Update frame failed: {err_msg}")
        return bytearray(out_buf)

    def build_frame(
        self, can_id: int, signals: dict[str, float], *,
        dlc: int = 8, extended: bool = False,
    ) -> bytearray:
        """Build a CAN frame from signal values.

        Works both inside and outside streaming mode.
        Starts with a zero-filled frame and encodes the given signals.

        Args:
            can_id: CAN message ID
            signals: Signal values to encode (name -> value)
            dlc: Data Length Code (0-15). Defaults to 8 (classic CAN).
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
        indices, nums, dens = self._resolve_signal_indices(
            signals, can_id, extended, "BuildFrame",
        )
        expected_bytes = dlc_to_bytes(dlc)
        n_signals = len(indices)
        out_buf = (ctypes.c_uint8 * expected_bytes)()
        out_err = ctypes.c_char_p()
        status = self._lib.aletheia_build_frame_bin(
            self._state,
            ctypes.c_uint32(can_id),
            ctypes.c_uint8(1 if extended else 0),
            ctypes.c_uint8(dlc),
            ctypes.c_uint32(n_signals),
            (ctypes.c_uint32 * n_signals)(*indices),
            (ctypes.c_int64 * n_signals)(*nums),
            (ctypes.c_int64 * n_signals)(*dens),
            out_buf,
            ctypes.byref(out_err),
        )
        if status != 0:
            err_msg = out_err.value.decode("utf-8") if out_err.value else "Unknown error"
            if out_err.value:
                self._lib.aletheia_free_str(out_err)
            raise ProcessError(f"Build frame failed: {err_msg}")
        return bytearray(out_buf)

    @override
    def __repr__(self) -> str:
        return "AletheiaClient()"
