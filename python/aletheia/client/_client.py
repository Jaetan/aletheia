"""AletheiaClient — streaming LTL checking and signal operations via FFI."""

from __future__ import annotations

import logging
from typing import TYPE_CHECKING, Self, cast, override

from aletheia.client._backend import Backend, FFIBackend
from aletheia.client._enrichment import build_diagnostic
from aletheia.client._ffi import parse_json_object
from aletheia.client._helpers.dbc_normalize import normalize_dbc, normalize_dbc_for_wire
from aletheia.client._helpers.rational import coerce_to_rational
from aletheia.client._log import LogEvent, log_event
from aletheia.client._response_parsers import (
    parse_parsed_dbc_response,
    parse_success_or_error,
    validate_issue_severities,
)
from aletheia.client._signal_ops import SignalOpsMixin
from aletheia.client._streaming import StreamingMixin
from aletheia.client._types import (
    FFIError,
    InputBoundExceededError,
    PropertyDiagnostic,
    ProtocolError,
    SignalLookup,
    StateError,
    StreamCaches,
    ValidationError,
)
from aletheia.limits import BOUND_KIND_INPUT_LENGTH_BYTES, MAX_DBC_TEXT_BYTES, MAX_JSON_BYTES
from aletheia.protocols import (
    Command,
    DBCDefinition,
    ErrorResponse,
    FormatDBCTextCommand,
    LTLFormula,
    ParseDBCCommand,
    ParseDBCTextCommand,
    ParsedDBCResponse,
    Response,
    SetPropertiesCommand,
    SuccessResponse,
    ValidateDBCCommand,
    ValidationResponse,
    dump_json,
    is_str_dict,
)

if TYPE_CHECKING:
    from collections.abc import Callable, Mapping
    from fractions import Fraction

    from aletheia.checks import CheckResult

_logger = logging.getLogger("aletheia")


def _send_frame_unbound(*_args: object, **_kwargs: object) -> bytes:
    """Stub assigned to ``_send_frame_binary`` before ``__enter__`` runs.

    Replaced in :meth:`AletheiaClient.__enter__` with the backend's actual
    bound method (a hot-path optimisation that dodges the
    ``self._backend.send_frame_binary`` two-attribute lookup per frame).
    If a caller bypasses ``__enter__`` and invokes ``send_frame`` directly,
    this stub raises :class:`StateError` so the failure is loud rather
    than ``NoneType is not callable``.
    """
    msg = "Client not initialized — use 'with' statement"
    raise StateError(msg)


class AletheiaClient(SignalOpsMixin, StreamingMixin):  # pylint: disable=too-many-instance-attributes
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
            None if backend is not None else (lambda rc=rts_cores: FFIBackend(rts_cores=rc))
        )
        # Hot-path send_frame_binary bound method; rebound on __enter__,
        # cleared back to the stub on ``close()``.
        self._send_frame_binary: Callable[..., bytes] = _send_frame_unbound

    def __enter__(self) -> Self:
        """Construct the FFIBackend (if not injected), initialize state."""
        if self._backend is None:
            make_backend = self._make_backend
            if make_backend is None:  # invariant: factory set whenever backend unset
                msg = "Client backend factory missing — constructed without a backend?"
                raise StateError(msg)
            self._backend = make_backend()
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
            msg = "Client not initialized — use 'with' statement"
            raise StateError(msg)

        json_bytes = dump_json(command).encode("utf-8")
        if len(json_bytes) > MAX_JSON_BYTES:
            raise InputBoundExceededError(
                BOUND_KIND_INPUT_LENGTH_BYTES,
                len(json_bytes),
                MAX_JSON_BYTES,
                code="input_bound_exceeded",
            )
        result_bytes = self._backend.process(self._state, json_bytes)
        return cast("Response", parse_json_object(result_bytes.decode("utf-8")))

    def _resolve_signal_indices(
        self,
        signals: Mapping[str, float | Fraction],
        can_id: int,
        cmd_name: str,
        *,
        extended: bool,
    ) -> tuple[tuple[int, ...], tuple[int, ...], tuple[int, ...]]:
        """Resolve signal names to (indices, numerators, denominators).

        Accepts float or Fraction inputs — Fraction flows through losslessly
        via ``coerce_to_rational``, matching the Agda core's ℚ arithmetic.
        """
        lookup = self._signal_lookup.get((can_id, extended))
        if lookup is None:
            if not self._signal_lookup:
                msg = f"{cmd_name}: DBC not loaded (call parse_dbc first)"
                raise StateError(msg)
            msg = f"{cmd_name}: no DBC message for CAN ID {can_id}"
            raise ValidationError(msg)
        indices: list[int] = []
        nums: list[int] = []
        dens: list[int] = []
        for name, value in signals.items():
            idx = lookup.indices.get(name)
            if idx is None:
                msg = f"{cmd_name}: unknown signal '{name}'"
                raise ValidationError(msg)
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
        self,
        result: ParsedDBCResponse | ErrorResponse,
    ) -> ParsedDBCResponse | ErrorResponse:
        """Log + populate the signal-name cache when the parse succeeded."""
        if result["status"] == "success":
            log_event(
                _logger,
                logging.INFO,
                LogEvent.DBC_PARSED,
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
            vresp = cast("ValidationResponse", response)
            return {
                "status": "validation",
                "has_errors": vresp["has_errors"],
                "issues": validate_issue_severities(list(vresp["issues"])),
            }

        if status == "error":
            message = response.get("message", "Unknown error")
            code = response.get("code")
            msg = f"validateDBC failed: {message}"
            raise ProtocolError(
                msg,
                code=code if isinstance(code, str) else None,
            )

        msg = f"Unexpected response status: {status!r} (expected 'validation' or 'error')"
        raise ProtocolError(msg)

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
            msg = "Client not initialized — use 'with' statement"
            raise StateError(msg)
        response_bytes = self._backend.format_dbc_binary(self._state)
        response = cast("Response", parse_json_object(response_bytes.decode("utf-8")))
        status = response.get("status")

        if status == "success":
            dbc = response.get("dbc")
            if not is_str_dict(dbc):
                msg = "Expected 'dbc' field in formatDBC response"
                raise ProtocolError(msg)
            return normalize_dbc(dbc)

        if status == "error":
            message = response.get("message", "Unknown error")
            code = response.get("code")
            msg = f"formatDBC failed: {message}"
            raise ProtocolError(
                msg,
                code=code if isinstance(code, str) else None,
            )

        msg = f"Unexpected response status: {status!r} (expected 'success' or 'error')"
        raise ProtocolError(msg)

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
                msg = "Expected 'text' field in formatDBCText response"
                raise ProtocolError(msg)
            return text

        if status == "error":
            message = response.get("message", "Unknown error")
            code = response.get("code")
            msg = f"formatDBCText failed: {message}"
            raise ProtocolError(
                msg,
                code=code if isinstance(code, str) else None,
            )

        msg = f"Unexpected response status: {status!r} (expected 'success' or 'error')"
        raise ProtocolError(msg)

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
            "properties": properties,
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
                _logger,
                logging.INFO,
                LogEvent.PROPERTIES_SET,
                count=len(properties),
            )
        return response

    def add_checks(
        self,
        checks: list[CheckResult],
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
    # Signal Operations — extract_signals / update_frame / build_frame —
    # are implemented in :mod:`._signal_ops` (mixin class).
    # =========================================================================

    @override
    def __repr__(self) -> str:
        return "AletheiaClient()"
