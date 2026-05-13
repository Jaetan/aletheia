"""Signal operations mixin for :class:`aletheia.AletheiaClient`.

Hosts ``extract_signals`` / ``update_frame`` / ``build_frame`` so the
streaming-and-DBC core in ``_client.py`` stays under the configured
module size threshold. Pure split — no behavioral change. The mixin
relies on the host class providing the same private state attributes
(``_backend``, ``_state``, ``_signal_lookup``, ``_resolve_signal_indices``)
that the original methods used in-place.
"""

from __future__ import annotations

import logging
from abc import ABC, abstractmethod
from collections.abc import Mapping
from fractions import Fraction
from typing import cast

from ..protocols import DLCCode, Response, is_object_list
from ._backend import Backend, BinaryPathUnsupportedError
from ._client_bin import parse_extraction_buffer
from ._ffi import parse_json_object
from ._helpers import (
    parse_absent_list,
    parse_errors_list,
    parse_values_list,
)
from ._log import LogEvent, log_event
from ._types import (
    ProtocolError,
    SignalExtractionResult,
    SignalLookup,
    StateError,
    dlc_to_bytes,
    validate_can_id,
    validate_payload_length,
)


_logger = logging.getLogger("aletheia")


class SignalOpsMixin(ABC):
    """Signal-extraction, frame-update, and frame-build methods.

    Mixed into :class:`aletheia.AletheiaClient`. All three methods work
    both inside and outside streaming mode. The class-level annotations
    + abstract methods below declare the private state surface the mixin
    reads / calls — actual values and bodies are provided by
    :class:`aletheia.AletheiaClient`. Using ``ABC`` + ``@abstractmethod``
    lets pyright trust the access paths as in-class while pylint
    recognises the stubs as legitimate forward declarations.
    """

    _backend: Backend | None
    _state: int | None
    _signal_lookup: dict[tuple[int, bool], SignalLookup]

    @abstractmethod
    def _resolve_signal_indices(
        self, signals: Mapping[str, float | Fraction],
        can_id: int, extended: bool, cmd_name: str,
    ) -> tuple[tuple[int, ...], tuple[int, ...], tuple[int, ...]]:
        """Resolve signal name → (indices, numerators, denominators)."""

    def extract_signals(
        self, can_id: int, dlc: DLCCode, data: bytes | bytearray,
        *, extended: bool = False,
    ) -> SignalExtractionResult:
        """Extract all signals from a CAN frame.

        Args:
            can_id: CAN message ID
            dlc: DLC code (0-8 for CAN 2.0B, 0-15 for CAN-FD)
            data: Frame payload
            extended: True for 29-bit extended CAN ID, False for 11-bit standard

        Returns:
            SignalExtractionResult with values/errors/absent partitioning

        Raises:
            ProtocolError: If the kernel rejects the extraction request
            ValidationError: If dlc is outside 0-15
        """
        if self._backend is None or self._state is None:
            raise StateError("Client not initialized — use 'with' statement")
        validate_payload_length(dlc, data)
        validate_can_id(can_id, extended=extended)

        # Use binary path when signal name cache is populated.  MockBackend
        # raises BinaryPathUnsupportedError to fall through to the JSON
        # path (cross-binding parity with Go's ErrBinaryPathUnsupported
        # contract in client.go:447).
        lookup = self._signal_lookup.get((can_id, extended))
        if lookup is not None:
            try:
                buf = self._backend.extract_signals_bin(
                    self._state,
                    can_id=can_id, extended=extended, dlc=dlc, data=data,
                )
            except BinaryPathUnsupportedError:
                pass
            else:
                return parse_extraction_buffer(buf, lookup.names)

        # JSON path (no DBC lookup OR backend without binary-bin support).
        try:
            response_bytes = self._backend.extract_signals_binary(
                self._state,
                can_id=can_id, extended=extended, dlc=dlc, data=data,
            )
            response = cast(Response, parse_json_object(response_bytes.decode("utf-8")))
        except ProtocolError as exc:
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
                canId=can_id, error=cast(str, error_msg),
            )
            # Forward the Agda wire ``code`` so callers can branch on e.g.
            # ``extraction_bit_extraction_failed`` vs ``frame_signal_not_found``
            # without parsing the message string (matches Go / C++ bindings).
            raise ProtocolError(
                f"extract_signals failed: {error_msg}", code=error_code,
            )
        if response.get("status") != "success":
            raise ProtocolError(f"Unexpected status: {response.get('status')}")

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
        dlc: DLCCode,
        frame: bytes | bytearray,
        signals: Mapping[str, float | Fraction],
        *,
        extended: bool = False,
    ) -> bytearray:
        """Update specific signals in an existing frame.

        Immutable — returns new frame, original unchanged.

        Args:
            can_id: CAN message ID
            dlc: DLC code (0-8 for CAN 2.0B, 0-15 for CAN-FD)
            frame: Existing frame data
            signals: Signal updates (name -> value)
            extended: True for 29-bit extended CAN ID

        Returns:
            New frame with updated signals
        """
        if self._backend is None or self._state is None:
            raise StateError("Client not initialized — use 'with' statement")
        expected_bytes = validate_payload_length(dlc, frame)
        validate_can_id(can_id, extended=extended)
        indices, nums, dens = self._resolve_signal_indices(
            signals, can_id, extended, "update_frame",
        )
        return bytearray(self._backend.update_frame_bin(
            self._state,
            can_id=can_id, extended=extended, dlc=dlc, data=frame,
            indices=indices, numerators=nums, denominators=dens,
            expected_bytes=expected_bytes,
        ))

    def build_frame(
        self,
        can_id: int,
        dlc: DLCCode,
        signals: Mapping[str, float | Fraction],
        *,
        extended: bool = False,
    ) -> bytearray:
        """Build a CAN frame from signal values (zero-filled base).

        Args:
            can_id: CAN message ID
            dlc: Data Length Code (0-15).
            signals: Signal values to encode (name -> value)
            extended: True for 29-bit extended CAN ID

        Returns:
            CAN frame payload (length = dlc_to_bytes(dlc))
        """
        if self._backend is None or self._state is None:
            raise StateError("Client not initialized — use 'with' statement")
        validate_can_id(can_id, extended=extended)
        indices, nums, dens = self._resolve_signal_indices(
            signals, can_id, extended, "build_frame",
        )
        return bytearray(self._backend.build_frame_bin(
            self._state,
            can_id=can_id, extended=extended, dlc=dlc,
            indices=indices, numerators=nums, denominators=dens,
            expected_bytes=dlc_to_bytes(dlc),
        ))
