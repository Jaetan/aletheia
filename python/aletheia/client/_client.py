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
    PropertyDiagnostic,
    ExtractionCache,
    MAX_EXTRACT_CACHE,
    dlc_to_bytes,
)

if TYPE_CHECKING:
    from ..checks import CheckResult


# ============================================================================
# Formula enrichment (module-level, testable without client)
# ============================================================================

def _format_predicate(pred: dict[str, object]) -> str:  # pylint: disable=too-many-return-statements
    """Format a predicate dict as a human-readable string."""
    kind = pred.get("predicate")
    signal = str(pred.get("signal", ""))
    if kind == "equals":
        return f"{signal} = {pred['value']:g}"
    if kind == "lessThan":
        return f"{signal} < {pred['value']:g}"
    if kind == "greaterThan":
        return f"{signal} > {pred['value']:g}"
    if kind == "lessThanOrEqual":
        return f"{signal} <= {pred['value']:g}"
    if kind == "greaterThanOrEqual":
        return f"{signal} >= {pred['value']:g}"
    if kind == "between":
        return f"{pred['min']:g} <= {signal} <= {pred['max']:g}"
    if kind == "changedBy":
        return f"|\u0394{signal}| > {pred['delta']:g}"
    return "<unknown predicate>"


def _format_timebound(ms: int) -> str:
    """Format milliseconds as a human-readable time bound."""
    if ms % 1_000 == 0:
        return f"{ms // 1_000}s "
    return f"{ms}ms "


def _format_formula(formula: dict[str, object]) -> str:  # pylint: disable=too-many-return-statements,too-many-branches
    """Format an LTL formula dict as a human-readable string."""
    op = formula.get("operator")
    if op == "atomic":
        return _format_predicate(cast(dict[str, object], formula["predicate"]))
    if op == "not":
        return "not(" + _format_formula(cast(dict[str, object], formula["formula"])) + ")"
    if op == "and":
        return (_format_formula(cast(dict[str, object], formula["left"]))
                + " and "
                + _format_formula(cast(dict[str, object], formula["right"])))
    if op == "or":
        return (_format_formula(cast(dict[str, object], formula["left"]))
                + " or "
                + _format_formula(cast(dict[str, object], formula["right"])))
    if op == "next":
        return "next(" + _format_formula(cast(dict[str, object], formula["formula"])) + ")"
    if op == "always":
        inner = cast(dict[str, object], formula["formula"])
        # Detect Never pattern: always(not(atomic(p)))
        if inner.get("operator") == "not":
            inner_not = cast(dict[str, object], inner["formula"])
            if inner_not.get("operator") == "atomic":
                return "never " + _format_predicate(cast(dict[str, object], inner_not["predicate"]))
        return "always(" + _format_formula(inner) + ")"
    if op == "eventually":
        return "eventually(" + _format_formula(cast(dict[str, object], formula["formula"])) + ")"
    if op == "until":
        return (_format_formula(cast(dict[str, object], formula["left"]))
                + " until "
                + _format_formula(cast(dict[str, object], formula["right"])))
    if op == "release":
        return (_format_formula(cast(dict[str, object], formula["left"]))
                + " release "
                + _format_formula(cast(dict[str, object], formula["right"])))
    if op == "metricAlways":
        tb = _format_timebound(int(formula["timebound"]))  # type: ignore[arg-type]
        return ("always within " + tb + "("
                + _format_formula(cast(dict[str, object], formula["formula"])) + ")")
    if op == "metricEventually":
        tb = _format_timebound(int(formula["timebound"]))  # type: ignore[arg-type]
        return ("eventually within " + tb + "("
                + _format_formula(cast(dict[str, object], formula["formula"])) + ")")
    if op == "metricUntil":
        tb = _format_timebound(int(formula["timebound"]))  # type: ignore[arg-type]
        return (_format_formula(cast(dict[str, object], formula["left"]))
                + " until within " + tb + " "
                + _format_formula(cast(dict[str, object], formula["right"])))
    if op == "metricRelease":
        tb = _format_timebound(int(formula["timebound"]))  # type: ignore[arg-type]
        return (_format_formula(cast(dict[str, object], formula["left"]))
                + " release within " + tb + " "
                + _format_formula(cast(dict[str, object], formula["right"])))
    return "<unknown>"


def _collect_signals(formula: dict[str, object]) -> list[str]:
    """Collect all signal names from a formula, deduplicated, in order."""
    signals: list[str] = []
    seen: set[str] = set()
    _collect_signals_into(formula, signals, seen)
    return signals


def _collect_signals_into(
    formula: dict[str, object], signals: list[str], seen: set[str],
) -> None:
    """Walk a formula collecting signal names."""
    op = formula.get("operator")
    if op == "atomic":
        pred = cast(dict[str, object], formula["predicate"])
        name = str(pred.get("signal", ""))
        if name and name not in seen:
            seen.add(name)
            signals.append(name)
    elif op in ("not", "next", "always", "eventually", "metricAlways", "metricEventually"):
        _collect_signals_into(cast(dict[str, object], formula["formula"]), signals, seen)
    elif op in ("and", "or", "until", "release", "metricUntil", "metricRelease"):
        _collect_signals_into(cast(dict[str, object], formula["left"]), signals, seen)
        _collect_signals_into(cast(dict[str, object], formula["right"]), signals, seen)


def _build_diagnostic(formula: LTLFormula) -> PropertyDiagnostic:
    """Build a PropertyDiagnostic from a formula. Always succeeds."""
    f = cast(dict[str, object], formula)
    return PropertyDiagnostic(
        signals=_collect_signals(f),
        formula_desc=_format_formula(f),
    )


def _format_enriched_reason(
    diag: PropertyDiagnostic, values: dict[str, float | None],
) -> str:
    """Build the enriched reason string."""
    parts: list[str] = []
    for sig in diag.signals:
        val = values.get(sig)
        if val is not None:
            parts.append(f"{sig} = {val:g}")
    if not parts:
        return "violated: " + diag.formula_desc
    return ", ".join(parts) + " (formula: " + diag.formula_desc + ")"


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
                self._diags[i] = _build_diagnostic(formula)
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
            return

        # Extract signal values (cached, bounded).
        cache_key: tuple[int, bytes] = (can_id, bytes(data))
        extraction: SignalExtractionResult | None = self._signal_cache.get(cache_key)
        if extraction is None:
            try:
                extraction = self.extract_signals(can_id=can_id, dlc=dlc, data=data)
                if len(self._signal_cache) < MAX_EXTRACT_CACHE:
                    self._signal_cache[cache_key] = extraction
            except (AletheiaError, ValueError):
                pass

        values: dict[str, float | None] = {}
        if extraction is not None:
            for sig in diag.signals:
                val = extraction.values.get(sig)
                if val is not None:
                    values[sig] = val

        result["signals"] = values
        result["formula"] = diag.formula_desc
        result["enriched_reason"] = _format_enriched_reason(diag, values)

    # Pre-encoded ack response bytes for fast-path comparison
    _ACK_BYTES = b'{"status":"ack"}'
    _ACK_BYTES_SPACED = b'{"status": "ack"}'

    def send_frame(
        self,
        timestamp: int,
        can_id: int,
        dlc: int,
        data: bytearray,
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
            if result_bytes == self._ACK_BYTES or result_bytes == self._ACK_BYTES_SPACED:
                return {"status": "ack"}

            # Slow path: violations/errors — full JSON parse
            result_str = result_bytes.decode("utf-8")
        finally:
            self._lib.aletheia_free_str(result_ptr)

        response = cast(Response, parse_json_object(result_str))
        result = self._parse_frame_response(response)

        if result["status"] == "violation":
            self._enrich_violation(result, can_id, dlc, data)

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
        frames: list[tuple[int, int, int, bytearray]],
        extended: bool = False,
    ) -> list[AckResponse | PropertyViolationResponse | ErrorResponse]:
        """Send multiple CAN frames in a batch.

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
            ProtocolError: If response status is unexpected
        """
        return [self.send_frame(ts, cid, dlc, d, extended=extended) for ts, cid, dlc, d in frames]

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
        result["formula"] = diag.formula_desc
        result["enriched_reason"] = "violated: " + diag.formula_desc

    # =========================================================================
    # Signal Operations (available anytime after DBC loaded)
    # =========================================================================

    def extract_signals(
        self, can_id: int, dlc: int, data: bytearray,
        extended: bool = False,
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
        """
        cmd: ExtractSignalsCommand = {
            "type": "command",
            "command": "extractAllSignals",
            "canId": can_id,
            "dlc": dlc,
            "data": list(data),
            "extended": extended,
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
        dlc: int,
        frame: bytearray,
        signals: dict[str, float],
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
        """
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
            "dlc": dlc,
            "data": list(frame),
            "signals": signals_json,
            "extended": extended,
        }
        response = self._send_command(cmd)

        if response.get("status") == "error":
            error_msg = response.get("message", "Unknown error")
            raise ProcessError(f"Update frame failed: {error_msg}")

        return self._parse_frame_data(
            cast(UpdateFrameResponse, response), dlc_to_bytes(dlc),
        )

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
            "dlc": dlc,
            "signals": signals_json,
            "extended": extended,
        }
        response = self._send_command(cmd)

        if response.get("status") == "error":
            error_msg = response.get("message", "Unknown error")
            raise ProcessError(f"Build frame failed: {error_msg}")

        return self._parse_frame_data(
            cast(BuildFrameResponse, response), dlc_to_bytes(dlc),
        )

    # =========================================================================
    # Helper methods for parsing responses
    # =========================================================================

    @staticmethod
    def _parse_frame_data(
        response: BuildFrameResponse | UpdateFrameResponse,
        expected_bytes: int,
    ) -> bytearray:
        """Extract and validate frame data from a response."""
        frame_data = response["data"]
        if len(frame_data) != expected_bytes:
            raise ProtocolError(
                f"Invalid frame data: expected {expected_bytes} bytes, "
                + f"got {len(frame_data)}"
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
