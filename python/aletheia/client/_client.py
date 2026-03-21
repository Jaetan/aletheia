"""AletheiaClient — streaming LTL checking and signal operations via FFI."""

from __future__ import annotations

import ctypes
import json
from typing import TYPE_CHECKING, Self, override, cast

from ..protocols import (
    DBCDefinition,
    DBCSignal,
    DBCMessage,
    LTLFormula,
    Command,
    Response,
    ParseDBCCommand,
    SetPropertiesCommand,
    StartStreamCommand,
    EndStreamCommand,
    DataFrame,
    BuildFrameCommand,
    BuildFrameResponse,
    ExtractSignalsCommand,
    UpdateFrameCommand,
    UpdateFrameResponse,
    ValidateDBCCommand,
    FormatDBCCommand,
    SuccessResponse,
    CompleteResponse,
    AckResponse,
    PropertyViolationResponse,
    PropertyResultEntry,
    ErrorResponse,
    ValidationIssue,
    ValidationResponse,
    RationalNumber,
    SignalValue,
    is_str_dict,
    is_object_list,
)
from ._ffi import parse_json_object, RTSState, find_ffi_library
from ._types import (
    AletheiaError,
    ProcessError,
    ProtocolError,
    SignalExtractionResult,
    CheckDiag,
    ExtractionCache,
    MAX_EXTRACT_CACHE,
)

if TYPE_CHECKING:
    from ..checks import CheckResult


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
       - set_properties() - Set LTL properties (before streaming)
       - set_check_diagnostics() - Register check metadata for enrichment
       - start_stream() - Enter streaming mode
       - send_frame() - Send frames for incremental checking
       - end_stream() - Exit streaming mode

    Signal operations work both inside and outside streaming mode.
    """

    def __init__(
        self,
        default_checks: list[CheckResult] | None = None,
        rts_cores: int = 1,
    ) -> None:
        self._lib: ctypes.CDLL | None = None
        self._state: ctypes.c_void_p | None = None
        self._diags: dict[int, CheckDiag] = {}
        self._signal_cache: ExtractionCache = {}
        self._default_checks: list[CheckResult] = list(default_checks) if default_checks else []
        self._rts_cores: int = rts_cores

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

        # Initialize GHC RTS (ref-counted, only first client actually calls hs_init)
        RTSState.acquire(self._lib, self._rts_cores)

        # Create Aletheia state
        self._state = ctypes.c_void_p(self._lib.aletheia_init())

        return self

    def close(self) -> None:
        """Free state and release RTS reference."""
        if self._lib is not None and self._state is not None:
            self._lib.aletheia_close(self._state)
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

    @staticmethod
    def _validate_rational(field_name: str, raw_value: object) -> RationalNumber:
        """Validate and extract RationalNumber from response field."""
        if isinstance(raw_value, int):
            return {"numerator": raw_value, "denominator": 1}
        if not is_str_dict(raw_value):
            raise ProtocolError(
                f"Expected {field_name} to be int or dict, got {type(raw_value).__name__}"
            )
        value_dict = raw_value
        numerator = value_dict.get("numerator")
        denominator = value_dict.get("denominator")
        if not isinstance(numerator, int):
            raise ProtocolError(f"Expected {field_name}.numerator to be int")
        if not isinstance(denominator, int):
            raise ProtocolError(f"Expected {field_name}.denominator to be int")
        if denominator == 0:
            raise ProtocolError(f"Expected {field_name}.denominator to be nonzero")
        return {"numerator": numerator, "denominator": denominator}

    @staticmethod
    def _parse_rational(value_raw: object) -> float:
        """Parse a value that may be a number, rational dict, or rational string."""
        if isinstance(value_raw, (int, float)):
            return float(value_raw)
        if is_str_dict(value_raw):
            numerator = value_raw.get("numerator")
            denominator = value_raw.get("denominator")
            if isinstance(numerator, int) and isinstance(denominator, int):
                if denominator == 0:
                    raise ProtocolError(
                        f"Division by zero in rational: {value_raw!r}"
                    )
                return numerator / denominator
        if isinstance(value_raw, str):
            if "/" in value_raw:
                parts = value_raw.split("/")
                if len(parts) == 2:
                    try:
                        numerator_s = int(parts[0])
                        denominator_s = int(parts[1])
                    except ValueError:
                        pass
                    else:
                        if denominator_s == 0:
                            raise ProtocolError(
                                f"Division by zero in rational string: {value_raw!r}"
                            )
                        return numerator_s / denominator_s
            try:
                return float(value_raw)
            except ValueError:
                pass
        raise ProtocolError(
            "Expected signal value to be number, rational dict, "
            + f"or rational string, got {type(value_raw).__name__}"
        )

    @staticmethod
    def _check_signal_value(name: str, value: float) -> None:
        """Guard against values that json.dumps encodes in scientific notation.

        Agda's JSON parser handles integers and decimals (e.g., 42, 3.14)
        but not exponent notation (e.g., 1.5e-10). Reject such values early
        with a clear error rather than getting a cryptic parse failure.
        """
        s = json.dumps(value)
        if "e" in s or "E" in s:
            raise ValueError(
                f"Signal value {value} for '{name}' would be JSON-encoded as {s}; "
                + "Agda's parser does not support scientific notation"
            )

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

        raise ProtocolError(f"Unexpected response status: {status}")

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
        return self._success_or_error(self._send_command(cmd))

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

        raise ProtocolError(f"Unexpected response status: {status}")

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
        cmd: FormatDBCCommand = {
            "type": "command",
            "command": "formatDBC",
        }
        response = self._send_command(cmd)
        status = response.get("status")

        if status == "success":
            dbc = response.get("dbc")
            if not is_str_dict(dbc):
                raise ProtocolError("Expected 'dbc' field in formatDBC response")
            return self._normalize_dbc(dbc)

        if status == "error":
            message = response.get("message", "Unknown error")
            raise ProtocolError(f"formatDBC failed: {message}")

        raise ProtocolError(f"Unexpected response status: {status}")

    # Fields in a DBCSignal that Agda serializes as JNumber (may be rational dict)
    _NUMERIC_SIGNAL_FIELDS = ("factor", "offset", "minimum", "maximum")

    @staticmethod
    def _normalize_signal(raw_sig: dict[str, object]) -> DBCSignal:
        """Normalize a single Agda signal dict into a DBCSignal."""
        sig: dict[str, object] = dict(raw_sig)
        for field in AletheiaClient._NUMERIC_SIGNAL_FIELDS:
            if field in sig:
                sig[field] = AletheiaClient._parse_rational(sig[field])
        return cast(DBCSignal, sig)

    @staticmethod
    def _normalize_message(raw_msg: dict[str, object]) -> DBCMessage:
        """Normalize a single Agda message dict into a DBCMessage."""
        raw_signals = raw_msg.get("signals")
        if not is_object_list(raw_signals):
            raise ProtocolError("Expected 'signals' to be a list")
        signals: list[DBCSignal] = []
        for s in raw_signals:
            if not is_str_dict(s):
                raise ProtocolError("Expected each signal to be a dict")
            signals.append(AletheiaClient._normalize_signal(s))
        msg: dict[str, object] = dict(raw_msg)
        msg["signals"] = signals
        return cast(DBCMessage, msg)

    @staticmethod
    def _normalize_dbc(raw: dict[str, object]) -> DBCDefinition:
        """Normalize Agda's formatDBC JSON into a proper DBCDefinition.

        Agda's ``formatRational`` encodes non-integer rationals as
        ``{"numerator": n, "denominator": d}`` dicts. This method
        converts those to ``float`` so the result matches the
        ``DBCDefinition`` TypedDict (where numeric fields are ``float``).
        """
        raw_messages = raw.get("messages")
        if not is_object_list(raw_messages):
            raise ProtocolError("Expected 'messages' to be a list")
        messages: list[DBCMessage] = []
        for m in raw_messages:
            if not is_str_dict(m):
                raise ProtocolError("Expected each message to be a dict")
            messages.append(AletheiaClient._normalize_message(m))
        return {
            "version": str(raw.get("version", "")),
            "messages": messages,
        }

    def set_properties(self, properties: list[LTLFormula]) -> SuccessResponse | ErrorResponse:
        """Set LTL properties to check. Must be called before start_stream().

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
        return self._success_or_error(self._send_command(cmd))

    def set_check_diagnostics(self, checks: list[CheckResult]) -> None:
        """Register check metadata for violation enrichment.

        When diagnostics are registered, ``send_frame()`` will automatically
        enrich ``PropertyViolationResponse`` with ``signal_name``,
        ``actual_value``, and ``condition`` fields by calling
        ``extract_signals`` (cached, bounded to 256 unique frames).

        Call this after ``set_properties()`` with the same check list.
        """
        self._diags.clear()
        self._signal_cache.clear()
        for i, check in enumerate(checks):
            sig = check.signal_name
            cond = check.condition_desc
            if sig and cond:
                self._diags[i] = CheckDiag(signal_name=sig, condition_desc=cond)

    def add_checks(
        self, checks: list[CheckResult],
    ) -> SuccessResponse | ErrorResponse:
        """Set LTL checks, merging with registered default checks.

        Combines ``default_checks`` (from constructor) with *checks*,
        calls ``set_properties()`` + ``set_check_diagnostics()`` atomically.

        Args:
            checks: Session-specific checks to add after defaults.

        Returns:
            SuccessResponse or ErrorResponse from ``set_properties()``.
        """
        all_checks = self._default_checks + checks
        response = self.set_properties([c.to_dict() for c in all_checks])
        if response["status"] == "success":
            self.set_check_diagnostics(all_checks)
        return response

    # =========================================================================
    # Streaming LTL Checking
    # =========================================================================

    def start_stream(self) -> SuccessResponse | ErrorResponse:
        """Start streaming mode for incremental LTL checking.

        Returns:
            SuccessResponse or ErrorResponse
        """
        self._signal_cache.clear()
        cmd: StartStreamCommand = {
            "type": "command",
            "command": "startStream"
        }
        return self._success_or_error(self._send_command(cmd))

    def _enrich_violation(
        self,
        result: PropertyViolationResponse,
        can_id: int,
        data: bytearray,
    ) -> None:
        """Enrich a violation response with signal diagnostics (in-place)."""
        if not self._diags:
            return
        prop_index_r = result["property_index"]
        idx = prop_index_r["numerator"] // prop_index_r["denominator"]
        diag = self._diags.get(idx)
        if diag is None:
            return

        result["signal_name"] = diag.signal_name
        result["condition"] = diag.condition_desc

        # Try to extract the actual signal value (cached, bounded).
        # Cache only successful extractions; failures fall back to Agda reason.
        cache_key: tuple[int, bytes] = (can_id, bytes(data))
        signals: SignalExtractionResult | None = self._signal_cache.get(cache_key)
        if signals is None and len(self._signal_cache) < MAX_EXTRACT_CACHE:
            try:
                signals = self.extract_signals(can_id=can_id, data=data)
                self._signal_cache[cache_key] = signals
            except (AletheiaError, ValueError):
                pass

        actual: float | None = None
        if signals is not None:
            actual = signals.values.get(diag.signal_name)
        result["actual_value"] = actual

        # Build enriched reason string
        if actual is not None:
            result["reason"] = (
                f"{diag.signal_name} = {actual} (limit: {diag.condition_desc})"
            )
        else:
            result["reason"] = (
                f"{diag.signal_name} violated {diag.condition_desc}"
            )

    def send_frame(
        self,
        timestamp: int,
        can_id: int,
        data: bytearray
    ) -> AckResponse | PropertyViolationResponse | ErrorResponse:
        """Send a CAN frame for incremental LTL checking.

        If check diagnostics have been registered via
        ``set_check_diagnostics()``, violation responses are automatically
        enriched with ``signal_name``, ``actual_value``, and ``condition``.

        Args:
            timestamp: Timestamp in microseconds
            can_id: CAN ID (11-bit standard or 29-bit extended)
            data: 8-byte payload

        Returns:
            AckResponse, PropertyViolationResponse, or ErrorResponse
        """
        if len(data) != 8:
            raise ValueError(f"Data must be exactly 8 bytes, got {len(data)}")

        frame: DataFrame = {
            "type": "data",
            "timestamp": timestamp,
            "id": can_id,
            "data": list(data),
        }
        response = self._send_command(frame)
        result = self._parse_frame_response(response)

        if result["status"] == "violation":
            self._enrich_violation(result, can_id, data)

        return result

    def _parse_frame_response(
        self, response: Response,
    ) -> AckResponse | PropertyViolationResponse | ErrorResponse:
        """Parse a single frame response into a typed result."""
        status = response.get("status")

        if status == "ack":
            return {"status": "ack"}

        if status == "violation":
            prop_type = response.get("type")
            if prop_type != "property":
                raise ProtocolError(f"Expected type='property', got {prop_type}")
            prop_index = self._validate_rational("property_index", response.get("property_index"))
            ts_rational = self._validate_rational("timestamp", response.get("timestamp"))
            result_violation: PropertyViolationResponse = {
                "status": "violation",
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

        raise ProtocolError(f"Unexpected response status: {status}")

    def send_frames_batch(
        self,
        frames: list[tuple[int, int, bytearray]]
    ) -> list[AckResponse | PropertyViolationResponse | ErrorResponse]:
        """Send multiple CAN frames in a batch.

        Args:
            frames: List of (timestamp, can_id, data) tuples where:
                - timestamp: Timestamp in microseconds
                - can_id: CAN ID (11-bit standard or 29-bit extended)
                - data: 8-byte payload

        Returns:
            List of responses in same order as input frames.

        Raises:
            ValueError: If any frame data is not exactly 8 bytes
            ProtocolError: If response status is unexpected
        """
        for i, (_, _, data) in enumerate(frames):
            if len(data) != 8:
                raise ValueError(f"Frame {i}: data must be exactly 8 bytes, got {len(data)}")

        results: list[AckResponse | PropertyViolationResponse | ErrorResponse] = []
        for ts, cid, d in frames:
            cmd: DataFrame = {"type": "data", "timestamp": ts, "id": cid, "data": list(d)}
            raw = self._send_command(cmd)
            result = self._parse_frame_response(raw)
            if result["status"] == "violation":
                self._enrich_violation(result, cid, d)
            results.append(result)
        return results

    def end_stream(self) -> CompleteResponse | ErrorResponse:
        """End streaming mode and finalize all properties.

        Returns:
            CompleteResponse with per-property finalization results, or
            ErrorResponse if not currently streaming.

        The ``results`` list contains one entry per property:
        - ``status="satisfaction"`` if the property held on the finite trace
        - ``status="violation"`` if the property failed at end-of-stream
          (e.g., safety property never resolved, liveness never satisfied)

        Violations are enriched with ``signal_name``, ``actual_value``, and
        ``condition`` when check diagnostics have been registered.
        """
        cmd: EndStreamCommand = {
            "type": "command",
            "command": "endStream"
        }
        response = self._send_command(cmd)
        status = response.get("status")
        message = response.get("message")

        if status == "complete":
            results = self._parse_finalization_results(response)
            return {"status": "complete", "results": results}

        if status == "error":
            result_error: ErrorResponse = {"status": "error", "message": ""}
            if isinstance(message, str):
                result_error["message"] = message
            return result_error

        raise ProtocolError(f"Unexpected response status: {status}")

    def _parse_finalization_results(
        self, response: Response,
    ) -> list[PropertyResultEntry]:
        """Parse end-of-stream property finalization results."""
        cresp = cast(CompleteResponse, response)
        raw_results = cresp["results"]
        entries: list[PropertyResultEntry] = []
        for raw in raw_results:
            entry_status = raw["status"]
            prop_index = self._validate_rational(
                "property_index", raw["property_index"],
            )
            result_entry: PropertyResultEntry = {
                "type": "property",
                "status": entry_status,
                "property_index": prop_index,
            }
            if entry_status == "violation":
                ts = raw.get("timestamp")
                if ts is not None:
                    result_entry["timestamp"] = self._validate_rational(
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
            return
        result["signal_name"] = diag.signal_name
        result["condition"] = diag.condition_desc

    # =========================================================================
    # Signal Operations (available anytime after DBC loaded)
    # =========================================================================

    def extract_signals(self, can_id: int, data: bytearray) -> SignalExtractionResult:
        """Extract all signals from a CAN frame.

        Works both inside and outside streaming mode.

        Args:
            can_id: CAN message ID
            data: 8-byte frame data

        Returns:
            SignalExtractionResult with values/errors/absent partitioning

        Raises:
            ValueError: If data is not exactly 8 bytes
            ProcessError: If extraction fails
        """
        if len(data) != 8:
            raise ValueError(f"Frame data must be 8 bytes, got {len(data)}")

        cmd: ExtractSignalsCommand = {
            "type": "command",
            "command": "extractAllSignals",
            "canId": can_id,
            "data": list(data)
        }
        response = self._send_command(cmd)

        if response.get("status") == "error":
            error_msg = response.get("message", "Unknown error")
            raise ProcessError(f"Extract signals failed: {error_msg}")

        # Parse response
        values_raw = response.get("values", [])
        if not is_object_list(values_raw):
            raise ProtocolError("Expected 'values' to be a list")
        values = self._parse_values_list(values_raw)

        errors_raw = response.get("errors", [])
        if not is_object_list(errors_raw):
            raise ProtocolError("Expected 'errors' to be a list")
        errors = self._parse_errors_list(errors_raw)

        absent_raw = response.get("absent", [])
        if not is_object_list(absent_raw):
            raise ProtocolError("Expected 'absent' to be a list")
        absent = self._parse_absent_list(absent_raw)

        return SignalExtractionResult(values=values, errors=errors, absent=absent)

    def update_frame(
        self,
        can_id: int,
        frame: bytearray,
        signals: dict[str, float]
    ) -> bytearray:
        """Update specific signals in an existing frame.

        Works both inside and outside streaming mode.
        Immutable - returns new frame, original unchanged.

        Args:
            can_id: CAN message ID
            frame: Existing 8-byte frame data
            signals: Signal updates (name -> value)

        Returns:
            New 8-byte frame with updated signals

        Raises:
            ValueError: If frame is not exactly 8 bytes
            ProcessError: If update fails
        """
        if len(frame) != 8:
            raise ValueError(f"Frame data must be 8 bytes, got {len(frame)}")

        for name, value in signals.items():
            self._check_signal_value(name, value)
        signals_json: list[SignalValue] = [
            {"name": name, "value": value}
            for name, value in signals.items()
        ]

        cmd: UpdateFrameCommand = {
            "type": "command",
            "command": "updateFrame",
            "canId": can_id,
            "data": list(frame),
            "signals": signals_json
        }
        response = self._send_command(cmd)

        if response.get("status") == "error":
            error_msg = response.get("message", "Unknown error")
            raise ProcessError(f"Update frame failed: {error_msg}")

        return self._parse_frame_data(cast(UpdateFrameResponse, response))

    def build_frame(self, can_id: int, signals: dict[str, float]) -> bytearray:
        """Build a CAN frame from signal values.

        Works both inside and outside streaming mode.
        Starts with a zero-filled frame and encodes the given signals.

        Args:
            can_id: CAN message ID
            signals: Signal values to encode (name -> value)

        Returns:
            8-byte CAN frame

        Raises:
            ProcessError: If frame building fails
        """
        for name, value in signals.items():
            self._check_signal_value(name, value)
        signals_json: list[SignalValue] = [
            {"name": name, "value": value}
            for name, value in signals.items()
        ]

        cmd: BuildFrameCommand = {
            "type": "command",
            "command": "buildFrame",
            "canId": can_id,
            "signals": signals_json
        }
        response = self._send_command(cmd)

        if response.get("status") == "error":
            error_msg = response.get("message", "Unknown error")
            raise ProcessError(f"Build frame failed: {error_msg}")

        return self._parse_frame_data(cast(BuildFrameResponse, response))

    # =========================================================================
    # Helper methods for parsing responses
    # =========================================================================

    @staticmethod
    def _parse_frame_data(response: BuildFrameResponse | UpdateFrameResponse) -> bytearray:
        """Extract and validate 8-byte frame data from a response."""
        frame_data = response["data"]
        if len(frame_data) != 8:
            raise ProtocolError(
                f"Invalid frame data: expected 8 bytes, got {len(frame_data)}"
            )
        return bytearray(frame_data)

    @staticmethod
    def _parse_values_list(values_data: list[object]) -> dict[str, float]:
        """Parse signal values list from response."""
        values: dict[str, float] = {}
        for item in values_data:
            if not is_str_dict(item):
                raise ProtocolError(f"Expected signal value to be dict, got {type(item)}")
            name_raw = item.get("name")
            if not isinstance(name_raw, str):
                raise ProtocolError(f"Expected signal name to be str, got {type(name_raw)}")
            value_raw = item.get("value")
            values[name_raw] = AletheiaClient._parse_rational(value_raw)
        return values

    @staticmethod
    def _parse_errors_list(errors_data: list[object]) -> dict[str, str]:
        """Parse signal errors list from response."""
        errors: dict[str, str] = {}
        for item in errors_data:
            if not is_str_dict(item):
                raise ProtocolError(f"Expected error item to be dict, got {type(item)}")
            name_raw = item.get("name")
            if not isinstance(name_raw, str):
                raise ProtocolError(f"Expected error signal name to be str, got {type(name_raw)}")
            error_raw = item.get("error")
            if not isinstance(error_raw, str):
                raise ProtocolError(f"Expected error message to be str, got {type(error_raw)}")
            errors[name_raw] = error_raw
        return errors

    @staticmethod
    def _parse_absent_list(absent_data: list[object]) -> list[str]:
        """Parse absent signals list from response."""
        absent: list[str] = []
        for item in absent_data:
            if not isinstance(item, str):
                raise ProtocolError(f"Expected absent signal name to be str, got {type(item)}")
            absent.append(item)
        return absent

    @override
    def __repr__(self) -> str:
        return "AletheiaClient()"
