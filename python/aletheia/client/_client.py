"""AletheiaClient — streaming LTL checking and signal operations via FFI."""

from __future__ import annotations

import logging
from collections.abc import Callable, Generator, Iterable, Mapping
from fractions import Fraction
from typing import TYPE_CHECKING, Self, override, cast

from ..protocols import (
    DBCDefinition,
    DLCCode,
    LTLFormula,
    Command,
    Response,
    RationalNumber,
    ParseDBCCommand,
    ParseDBCTextCommand,
    FormatDBCTextCommand,
    SetPropertiesCommand,
    ValidateDBCCommand,
    SuccessResponse,
    AckResponse,
    PropertyViolationResponse,
    PropertyResultEntry,
    CompleteResponse,
    CompleteWarning,
    ErrorResponse,
    ValidationResponse,
    ParsedDBCResponse,
    is_str_dict,
)
from ._backend import Backend, FFIBackend
from ._client_bin import FrameIdentity
from ._enrichment import build_diagnostic, format_enriched_reason
from ._ffi import parse_json_object
from ..protocols import dump_json
from ._helpers.dbc_normalize import normalize_dbc, normalize_dbc_for_wire
from ._helpers.rational import coerce_to_rational
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
from ._signal_ops import SignalOpsMixin
from ._types import (
    AletheiaError,
    CANFrameTuple,
    FFIError,
    FrameResult,
    InputBoundExceededError,
    PropertyDiagnostic,
    ProtocolError,
    SignalExtractionResult,
    SignalLookup,
    StateError,
    StreamCaches,
    ValidationError,
    MAX_EXTRACT_CACHE,
    call_send_frame,
    validate_can_id,
    validate_payload_length,
)
from ..limits import BOUND_KIND_INPUT_LENGTH_BYTES, MAX_DBC_TEXT_BYTES, MAX_JSON_BYTES

if TYPE_CHECKING:
    from ..checks import CheckResult

_logger = logging.getLogger("aletheia")


def _rational_index(r: RationalNumber, context: str) -> int:
    """Convert a rational property_index to int, raising on zero denominator."""
    if r["denominator"] == 0:
        raise ProtocolError(f"Zero denominator in {context} property_index")
    return r["numerator"] // r["denominator"]


def _send_frame_unbound(*_args: object, **_kwargs: object) -> bytes:
    """Stub assigned to ``_send_frame_binary`` before ``__enter__`` runs.

    Replaced in :meth:`AletheiaClient.__enter__` with the backend's actual
    bound method (a hot-path optimisation that dodges the
    ``self._backend.send_frame_binary`` two-attribute lookup per frame).
    If a caller bypasses ``__enter__`` and invokes ``send_frame`` directly,
    this stub raises :class:`StateError` so the failure is loud rather
    than ``NoneType is not callable``.
    """
    raise StateError("Client not initialized — use 'with' statement")


class AletheiaClient(SignalOpsMixin):  # pylint: disable=too-many-instance-attributes
    """Client for streaming LTL checking and signal operations.

    Calls the formally verified Agda core via a :class:`Backend` —
    :class:`FFIBackend` in production (wraps ``libaletheia-ffi.so`` via
    ``ctypes``), :class:`MockBackend` in tests.  The DI seam closes
    cross-binding parity with Go ``aletheia.Backend`` and C++
    ``aletheia::IBackend`` (R20 cluster P).

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

    Streaming adequacy (``Unsure`` / ``unresolved`` verdicts):

    The streaming evaluator is **sound** but requires that every property's
    target signal is observed in the input trace at least once — the
    ``AllObserved`` invariant from
    ``Aletheia.Protocol.Adequacy.StreamingWarm.streaming-warms-cache``.
    This is a **user obligation** on the trace; the FFI does not check it.

    When the obligation is violated (e.g., a property references a signal
    that no frame in the trace carries), the property may finalize as
    ``status="unresolved"`` — the three-valued Kleene ``Unsure`` — rather
    than ``"satisfied"`` / ``"violated"``. Reported verdicts remain sound;
    coverage is the caller's responsibility.

    See ``docs/architecture/PROTOCOL.md`` § Streaming Semantics: Soundness
    vs. Completeness for the full contract.
    """

    def __init__(
        self,
        default_checks: list[CheckResult] | None = None,
        rts_cores: int = 1,
        *,
        backend: Backend | None = None,
    ) -> None:
        """Initialize a client.

        Args:
            default_checks: Pre-built checks applied on every ``start_stream``
                call. Shallow-copied; **do not** mutate originals after passing.
            rts_cores: GHC RTS capabilities (default 1). Mismatch across
                clients logs a warning.  Ignored when ``backend`` is
                non-None (the injected backend already owns RTS state).
            backend: Optional :class:`Backend` for dependency injection.
                When ``None`` (default), a :class:`FFIBackend` is
                constructed on ``__enter__`` from the resolved
                ``libaletheia-ffi.so`` path.  Pass a :class:`MockBackend`
                instance to drive tests without loading the shared
                library; cross-binding parity with Go ``WithBackend`` /
                C++ ``AletheiaClient(unique_ptr<IBackend>)``.
        """
        self._backend: Backend | None = backend
        self._state: int | None = None
        self._diags: dict[int, PropertyDiagnostic] = {}
        self._caches = StreamCaches()
        self._default_checks: list[CheckResult] = list(default_checks) if default_checks else []
        # Per-message signal name/index lookup, populated by ``parse_dbc``.
        self._signal_lookup: dict[tuple[int, bool], SignalLookup] = {}
        # Backend factory: non-None iff the Client owns the backend
        # lifecycle (closes over rts_cores; cleared on ``close()``).
        # User-injected backends are caller-owned: factory stays None.
        self._make_backend: Callable[[], Backend] | None = (
            None if backend is not None
            else (lambda rc=rts_cores: FFIBackend(rts_cores=rc))
        )
        # Hot-path send_frame_binary bound method; rebound on __enter__,
        # cleared back to the stub on ``close()``.
        self._send_frame_binary: Callable[..., bytes] = _send_frame_unbound

    def __enter__(self) -> Self:
        """Construct the FFIBackend (if not injected), initialize state."""
        if self._backend is None:
            assert self._make_backend is not None
            self._backend = self._make_backend()
        self._state = self._backend.init()
        # Cache the hot-path bound method to skip per-frame
        # `self._backend.send_frame_binary` attribute lookup.  Set on
        # __enter__ so a test that wraps the backend BEFORE construction
        # picks up the wrapped instance's bound method.
        self._send_frame_binary = self._backend.send_frame_binary
        return self

    def close(self) -> None:
        """Free state and release RTS reference."""
        try:
            if self._backend is not None and self._state is not None:
                self._backend.close(self._state)
        finally:
            self._state = None
            self._send_frame_binary = _send_frame_unbound
            # Only drop the backend reference when the Client constructed
            # it; user-injected backends are caller-owned.
            if self._make_backend is not None:
                self._backend = None

    @property
    def is_closed(self) -> bool:
        """True after ``close()`` (or ``__exit__``) has run.

        Mirrors the stdlib convention (``socket.socket`` / ``mmap.mmap``)
        of exposing a public predicate over the post-close invariant
        (state pointer cleared).  Lets stability / leak harnesses verify
        the cleanup pathway without reaching for the underlying ``_state``
        handle.
        """
        return self._state is None

    def __exit__(
        self,
        exc_type: type[BaseException] | None,
        exc_val: BaseException | None,
        exc_tb: object,
    ) -> None:
        self.close()

    def _send_command(self, command: Command) -> Response:
        """Send a JSON command via the Backend.

        Rejects oversize JSON payloads (`> MAX_JSON_BYTES`) with a typed
        :class:`InputBoundExceededError` before crossing the FFI boundary,
        per AGENTS.md universal rule "Adversarial-input bounds at parser
        surfaces".  The Agda kernel enforces the same bound; this is the
        binding's short-circuit so we do not allocate a 100 MB ctypes
        buffer only to be rejected on the other side.
        """
        if self._backend is None or self._state is None:
            raise StateError("Client not initialized — use 'with' statement")

        json_bytes = dump_json(command).encode("utf-8")
        if len(json_bytes) > MAX_JSON_BYTES:
            raise InputBoundExceededError(
                BOUND_KIND_INPUT_LENGTH_BYTES,
                len(json_bytes),
                MAX_JSON_BYTES,
                code="input_bound_exceeded",
            )
        result_bytes = self._backend.process(self._state, json_bytes)
        return cast(Response, parse_json_object(result_bytes.decode("utf-8")))

    def _resolve_signal_indices(
        self, signals: Mapping[str, float | Fraction],
        can_id: int, extended: bool, cmd_name: str,
    ) -> tuple[tuple[int, ...], tuple[int, ...], tuple[int, ...]]:
        """Resolve signal names to (indices, numerators, denominators).

        Accepts float or Fraction inputs — Fraction flows through losslessly
        via ``coerce_to_rational``, matching the Agda core's ℚ arithmetic.
        """
        lookup = self._signal_lookup.get((can_id, extended))
        if lookup is None:
            if not self._signal_lookup:
                raise StateError(f"{cmd_name}: DBC not loaded (call parse_dbc first)")
            raise ValidationError(f"{cmd_name}: no DBC message for CAN ID {can_id}")
        indices: list[int] = []
        nums: list[int] = []
        dens: list[int] = []
        for name, value in signals.items():
            idx = lookup.indices.get(name)
            if idx is None:
                raise ValidationError(f"{cmd_name}: unknown signal '{name}'")
            n, d = coerce_to_rational(value)
            indices.append(idx)
            nums.append(n)
            dens.append(d)
        return tuple(indices), tuple(nums), tuple(dens)

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
        cmd: ParseDBCCommand = {
            "type": "command",
            "command": "parseDBC",
            "dbc": normalize_dbc_for_wire(dbc),
        }
        return self._finalize_parsed_dbc(parse_parsed_dbc_response(self._send_command(cmd)))

    def parse_dbc_text(self, text: str) -> ParsedDBCResponse | ErrorResponse:
        """Parse and validate a DBC from raw .dbc file text via the Agda text parser.

        Mirrors :meth:`parse_dbc`'s response shape; both routes share the
        same Agda core post-B.3.f.

        Defense-in-depth (R19 cluster 8 — CPP-D-21.3 cross-binding parity):
        rejects DBC text inputs longer than :data:`MAX_DBC_TEXT_BYTES` before
        wrapping them in a JSON command, raising :class:`InputBoundExceededError`
        with code ``"input_bound_exceeded"``.  The outer
        :data:`MAX_JSON_BYTES` cap in :meth:`_send_command` still covers the
        wrapped command separately; the additional inner cap matches the
        Agda kernel's two-layer enforcement in ``handleParseDBCText``.
        """
        text_bytes = text.encode("utf-8")
        if len(text_bytes) > MAX_DBC_TEXT_BYTES:
            raise InputBoundExceededError(
                BOUND_KIND_INPUT_LENGTH_BYTES,
                len(text_bytes),
                MAX_DBC_TEXT_BYTES,
                code="input_bound_exceeded",
            )
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
            "dbc": normalize_dbc_for_wire(dbc),
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
            code = response.get("code")
            raise ProtocolError(
                f"validateDBC failed: {message}",
                code=code if isinstance(code, str) else None,
            )

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
        if self._backend is None or self._state is None:
            raise StateError("Client not initialized — use 'with' statement")
        response_bytes = self._backend.format_dbc_binary(self._state)
        response = cast(Response, parse_json_object(response_bytes.decode("utf-8")))
        status = response.get("status")

        if status == "success":
            dbc = response.get("dbc")
            if not is_str_dict(dbc):
                raise ProtocolError("Expected 'dbc' field in formatDBC response")
            return normalize_dbc(dbc)

        if status == "error":
            message = response.get("message", "Unknown error")
            code = response.get("code")
            raise ProtocolError(
                f"formatDBC failed: {message}",
                code=code if isinstance(code, str) else None,
            )

        raise ProtocolError(
            f"Unexpected response status: {status!r} (expected 'success' or 'error')"
        )

    def format_dbc_text(self, dbc: DBCDefinition) -> str:
        """Render a DBC JSON dict back to .dbc file text via the verified Agda formatter.

        Inverse of :meth:`parse_dbc_text` at the wire level: ``parse_dbc_text(
        format_dbc_text(d))`` returns ``d`` byte-identical for any well-formed
        DBC (Track E.9a coverage).  Does not modify client state — pass any
        ``DBCDefinition`` value (typically from :meth:`parse_dbc_text`,
        :meth:`format_dbc`, or :func:`aletheia.dbc_to_json`).

        Args:
            dbc: DBC definition dict in canonical Agda wire shape.

        Returns:
            String containing the .dbc file content.

        Raises:
            ProtocolError: If the JSON DBC fails Agda-side parsing or the
                response shape is unexpected.
        """
        cmd: FormatDBCTextCommand = {
            "type": "command",
            "command": "formatDBCText",
            "dbc": normalize_dbc_for_wire(dbc),
        }
        response = self._send_command(cmd)
        status = response.get("status")

        if status == "success":
            text = response.get("text")
            if not isinstance(text, str):
                raise ProtocolError("Expected 'text' field in formatDBCText response")
            return text

        if status == "error":
            message = response.get("message", "Unknown error")
            code = response.get("code")
            raise ProtocolError(
                f"formatDBCText failed: {message}",
                code=code if isinstance(code, str) else None,
            )

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
            SuccessResponse or ErrorResponse from the FFI ``setProperties``
            command.  The return value reflects only the kernel-side outcome;
            binding-internal failures while constructing per-property
            diagnostics surface via the ``Raises`` channel below — mirrors
            the C++ binding's ``Result<void>`` lowering at
            ``cpp/src/client.cpp::set_properties``.

        Raises:
            FFIError: The rational renderer cannot load
                ``libaletheia-ffi.so`` when ``build_diagnostic`` reaches
                ``_format_rational``.  Kernel-side properties have already
                been committed at this point; ``self._diags`` is cleared so
                subsequent stream iterations do not observe partial state.
            ValidationError: A formula contains a predicate value the
                kernel accepted but the Python rational renderer rejects
                (e.g. malformed ``{"numerator", "denominator"}`` dict).
                Same state-cleanup contract as ``FFIError``.
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
            try:
                for i, formula in enumerate(properties):
                    self._diags[i] = build_diagnostic(formula)
            except (FFIError, ValidationError):
                # build_diagnostic failed after the kernel accepted the
                # properties → drop partial diagnostics so subsequent
                # stream iterations don't observe an inconsistent view.
                self._diags.clear()
                raise
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
        if self._backend is None or self._state is None:
            raise StateError("Client not initialized — use 'with' statement")
        response_bytes = self._backend.start_stream_binary(self._state)
        response = parse_success_or_error(
            cast(Response, parse_json_object(response_bytes.decode("utf-8"))),
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

    # Pre-encoded ack-response shapes — compact form from the binary FFI
    # path; post-colon-space form from the JSON FFI path (what `json.dumps`
    # emits by default).  Hoisted to a class const so the streaming hot
    # path's membership test doesn't allocate a fresh 2-tuple per frame.
    _ACK_RESPONSES = (b'{"status":"ack"}', b'{"status": "ack"}')

    def send_frame(  # pylint: disable=too-many-arguments
        self,
        timestamp: int,
        can_id: int,
        dlc: DLCCode,
        data: bytes | bytearray,
        *,
        extended: bool = False,
        brs: bool | None = None,
        esi: bool | None = None,
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
            brs: CAN-FD Bit Rate Switch (ISO 11898-1:2015 §10.4.2);
                ``None`` for CAN 2.0B. Pass-through metadata — not consumed
                by the kernel; see :class:`aletheia.CANFrameTuple`.
            esi: CAN-FD Error State Indicator (ISO 11898-1:2015 §10.4.3);
                same semantics and pass-through status as ``brs``.

        Returns:
            AckResponse, PropertyViolationResponse, or ErrorResponse
        """
        if self._backend is None or self._state is None:
            raise StateError("Client not initialized — use 'with' statement")
        if timestamp < 0:
            raise ValidationError("timestamp must be non-negative")
        validate_can_id(can_id, extended=extended)
        validate_payload_length(dlc, data)  # validates dlc is in [0, 15]

        # Use the bound method cached at __enter__ to dodge per-frame
        # attribute-lookup cost on ``self._backend.send_frame_binary``.
        result_bytes = self._send_frame_binary(
            self._state,
            timestamp=timestamp, can_id=can_id, extended=extended,
            dlc=dlc, data=data, brs=brs, esi=esi,
        )

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
                    _logger, logging.DEBUG, LogEvent.FRAME_PROCESSED,
                    ts=timestamp, canId=can_id, extended=extended,
                    response="ack",
                )
            return {"status": "ack"}

        # Slow path: violations/errors — full JSON parse
        response = cast(Response, parse_json_object(result_bytes.decode("utf-8")))
        result = parse_frame_response(response)

        if result["status"] == "fails":
            self._enrich_violation(
                result, FrameIdentity(can_id, extended, dlc), data,
            )
            if _logger.isEnabledFor(logging.DEBUG):
                log_event(
                    _logger, logging.DEBUG, LogEvent.FRAME_PROCESSED,
                    ts=timestamp, canId=can_id, extended=extended,
                    response="violation",
                )
        else:
            if _logger.isEnabledFor(logging.DEBUG):
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
        for i, frame in enumerate(frames):
            results.append(call_send_frame(self.send_frame, i, frame, results))
        return results

    def send_frames_iter(
        self,
        frames: Iterable[CANFrameTuple],
    ) -> Generator[FrameResult, None, None]:
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
        None`` exposes the underlying ``PropertyViolationResponse``) and do
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
            yield FrameResult(
                frame_index=i, timestamp=frame.timestamp,
                can_id=frame.can_id, extended=frame.extended,
                response=call_send_frame(self.send_frame, i, frame, []),
            )

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
            raise StateError("Client not initialized — use 'with' statement")
        if timestamp < 0:
            raise ValidationError("timestamp must be non-negative")
        result_bytes = self._backend.send_error_binary(self._state, timestamp)
        if result_bytes in self._ACK_RESPONSES:
            log_event(
                _logger, logging.DEBUG, LogEvent.ERROR_EVENT_SENT,
                ts=timestamp, response="ack",
            )
            return {"status": "ack"}
        response = cast(Response, parse_json_object(result_bytes.decode("utf-8")))
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
        if self._backend is None or self._state is None:
            raise StateError("Client not initialized — use 'with' statement")
        if timestamp < 0:
            raise ValidationError("timestamp must be non-negative")
        validate_can_id(can_id, extended=extended)
        result_bytes = self._backend.send_remote_binary(
            self._state, timestamp=timestamp, can_id=can_id, extended=extended,
        )
        if result_bytes in self._ACK_RESPONSES:
            log_event(
                _logger, logging.DEBUG, LogEvent.REMOTE_EVENT_SENT,
                ts=timestamp, canId=can_id, extended=extended,
                response="ack",
            )
            return {"status": "ack"}
        response = cast(Response, parse_json_object(result_bytes.decode("utf-8")))
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
            raise StateError("Client not initialized — use 'with' statement")
        response_bytes = self._backend.end_stream_binary(self._state)
        response = cast(Response, parse_json_object(response_bytes.decode("utf-8")))
        status = response.get("status")

        if status == "complete":
            results = parse_finalization_results(
                response, self._enrich_finalization_result,
            )
            raw_warnings = cast(list[dict[str, object]], response.get("warnings", []))
            warnings: list[CompleteWarning] = [
                {
                    "kind": cast(str, w.get("kind", "")),
                    "property_index": cast(int, w.get("property_index", 0)),
                    "detail": cast(str, w.get("detail", "")),
                }
                for w in raw_warnings
            ]
            num_fails = sum(1 for r in results if r["status"] == "fails")
            num_unresolved = sum(1 for r in results if r["status"] == "unresolved")
            self._caches.last_frames.clear()
            for w in warnings:
                if w["kind"] == "uncached_atom":
                    log_event(
                        _logger, logging.WARNING, LogEvent.ENDSTREAM_UNCACHED_ATOM,
                        property_index=w["property_index"],
                        detail=w["detail"],
                    )
            log_event(
                _logger, logging.INFO, LogEvent.STREAM_ENDED,
                numResults=len(results), numFails=num_fails,
                numUnresolved=num_unresolved,
                numWarnings=len(warnings),
            )
            return {"status": "complete", "results": results, "warnings": warnings}

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
    # Signal Operations — extract_signals / update_frame / build_frame —
    # are implemented in :mod:`._signal_ops` (mixin class).
    # =========================================================================

    @override
    def __repr__(self) -> str:
        return "AletheiaClient()"
