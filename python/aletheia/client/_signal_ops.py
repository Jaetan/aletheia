"""Signal operations mixin for :class:`aletheia.AletheiaClient`.

Hosts ``extract_signals`` / ``update_frame`` / ``build_frame`` so the
streaming-and-DBC core in ``_client.py`` stays under the configured
module size threshold. Pure split — no behavioral change. The mixin
relies on the host class providing the same private state attributes
(``_lib``, ``_state``, ``_signal_lookup``, ``_resolve_signal_indices``,
``_parse_ffi_result``) that the original methods used in-place.
"""

from __future__ import annotations

import ctypes
import logging
from abc import ABC, abstractmethod
from collections.abc import Mapping
from fractions import Fraction
from typing import cast

from ..protocols import Response, is_object_list
from ._client_bin import BinaryFFI, FrameIdentity, SignalValues
from ._helpers import (
    parse_absent_list,
    parse_errors_list,
    parse_values_list,
)
from ._log import LogEvent, log_event
from ._types import (
    ProcessError,
    ProtocolError,
    SignalExtractionResult,
    SignalLookup,
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

    _lib: ctypes.CDLL | None
    _state: ctypes.c_void_p | None
    _signal_lookup: dict[tuple[int, bool], SignalLookup]

    @abstractmethod
    def _resolve_signal_indices(
        self, signals: Mapping[str, float | Fraction],
        can_id: int, extended: bool, cmd_name: str,
    ) -> SignalValues:
        """Resolve signal name → index via the host class's lookup cache."""

    @abstractmethod
    def _parse_ffi_result(self, result_ptr: int) -> Response:
        """Decode a JSON FFI response and free the C string."""

    def extract_signals(
        self, can_id: int, dlc: int, data: bytes | bytearray,
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
            ProcessError: If extraction fails
            ValueError: If dlc is outside 0-15
        """
        if self._lib is None or self._state is None:
            raise ProcessError("Client not initialized — use 'with' statement")
        validate_payload_length(dlc, data)
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

        # Fallback: JSON path. ctypes argtypes (set in configure_ffi_signatures)
        # auto-convert Python ints — explicit wrappers omitted to keep the call
        # site terse where the surrounding code is self-explanatory.
        result_ptr = self._lib.aletheia_extract_signals(
            self._state, can_id, 1 if extended else 0, dlc, data_array, len(data),
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
                canId=can_id, error=cast(str, error_msg),
            )
            # Forward the Agda wire ``code`` so callers can branch on e.g.
            # ``extraction_bit_extraction_failed`` vs ``frame_signal_not_found``
            # without parsing the message string (matches Go / C++ bindings).
            raise ProcessError(
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
        dlc: int,
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
        if self._lib is None or self._state is None:
            raise ProcessError("Client not initialized — use 'with' statement")
        expected_bytes = validate_payload_length(dlc, frame)
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
        self,
        can_id: int,
        dlc: int,
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
