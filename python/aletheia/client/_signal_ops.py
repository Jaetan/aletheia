# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
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
from abc import abstractmethod
from typing import TYPE_CHECKING, LiteralString

from aletheia.client._backend import Backend, BinaryPathUnsupportedError
from aletheia.client._client_bin import SignalValues, parse_extraction_buffer
from aletheia.client._ffi import KernelResponse, parse_json_object
from aletheia.client._helpers.json_codec import (
    parse_absent_list,
    parse_errors_list,
    parse_values_list,
)
from aletheia.client._helpers.reply_shape import (
    ARRAY,
    REPLY_ROOT,
    at,
    came,
    came_word,
    held,
    reply_refusal,
    words,
)
from aletheia.client._log import LogEvent, log_event
from aletheia.client._mixin_state import ClientHostState
from aletheia.client._refusal import envelope_message, read_error_code
from aletheia.client._types import (
    ProtocolError,
    SignalExtractionResult,
    SignalLookup,
    StateError,
    dlc_to_bytes,
    validate_can_id,
    validate_payload_length,
)

if TYPE_CHECKING:
    from collections.abc import Mapping
    from fractions import Fraction

    from aletheia.client._helpers.reply_shape import ReplyFields
    from aletheia.types import DLCCode, JSONValue

_logger = logging.getLogger("aletheia")


def _extraction_result(reply: ReplyFields) -> SignalExtractionResult:
    """Read an extraction success reply's three arrays, which the kernel always writes.

    Raises:
        ProtocolError: If ``values``, ``errors`` or ``absent`` is absent or not
            an array, or an entry of one is not what the kernel writes there.

    """
    return SignalExtractionResult(
        values=parse_values_list(_array(reply, "values")),
        errors=parse_errors_list(_array(reply, "errors")),
        absent=tuple(parse_absent_list(_array(reply, "absent"))),
    )


def _array(reply: ReplyFields, key: LiteralString) -> list[JSONValue]:
    """Read the array ``key`` holds at an extraction reply's root."""
    if key in reply and isinstance(value := reply[key], list):
        return value
    raise reply_refusal(at(REPLY_ROOT, key), ARRAY, came(reply, key))


class SignalOpsMixin(ClientHostState):
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
        self,
        signals: Mapping[str, int | Fraction],
        can_id: int,
        cmd_name: str,
        *,
        extended: bool,
    ) -> SignalValues:
        """Resolve signal names to their indices and values."""

    def extract_signals(
        self,
        can_id: int,
        dlc: DLCCode,
        data: bytes | bytearray,
        *,
        extended: bool = False,
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
        # One lock around the whole op: serializes the FFI call(s) on
        # ``self._state`` against ``close()`` (an async ``extract_signals``
        # cancelled mid-flight abandons its ``to_thread`` worker, which must
        # not race teardown freeing the StablePtr).  Uncontended in normal
        # use, so the longer hold is free — only the single acquire costs.
        with self._ffi_lock:
            if self._backend is None or self._state is None:
                msg = "Client not initialized — use 'with' statement"
                raise StateError(msg)
            validate_payload_length(dlc, data)
            validate_can_id(can_id, extended=extended)

            # Use binary path when signal name cache is populated.  MockBackend
            # raises BinaryPathUnsupportedError to fall through to the JSON
            # path (cross-binding parity with Go's ErrBinaryPathUnsupported
            # contract in client_stream.go, Client.ExtractSignals).
            lookup = self._signal_lookup.get((can_id, extended))
            if lookup is not None:
                try:
                    buf = self._backend.extract_signals_bin(
                        self._state,
                        can_id=can_id,
                        extended=extended,
                        dlc=dlc,
                        data=data,
                    )
                except BinaryPathUnsupportedError:
                    pass
                else:
                    return parse_extraction_buffer(buf, lookup.names)

            # JSON path (no DBC lookup OR backend without binary-bin support).
            try:
                response_bytes = self._backend.extract_signals_binary(
                    self._state,
                    can_id=can_id,
                    extended=extended,
                    dlc=dlc,
                    data=data,
                )
                reply = parse_json_object(KernelResponse(response_bytes))
            except ProtocolError as exc:
                log_event(
                    _logger,
                    logging.WARNING,
                    LogEvent.EXTRACTION_PROCESS_FAILED,
                    canId=can_id,
                    error=str(exc),
                )
                raise

            if held(reply, "status") == "error":
                error_code = read_error_code(reply)
                error_msg = envelope_message(reply)
                log_event(
                    _logger,
                    logging.WARNING,
                    LogEvent.EXTRACTION_PARSE_FAILED,
                    canId=can_id,
                    error=error_msg,
                )
                # Forward the Agda wire ``code`` so callers can branch on e.g.
                # ``parse_payload_length_mismatch`` vs ``frame_signal_not_found``
                # without parsing the message string (matches Go / C++ bindings).
                raise ProtocolError(error_msg, code=error_code)
            if held(reply, "status") != "success":
                raise reply_refusal(
                    at(REPLY_ROOT, "status"), words("success", "error"), came_word(reply, "status")
                )

            return _extraction_result(reply)

    def update_frame(  # pylint: disable=too-many-arguments
        self,
        can_id: int,
        dlc: DLCCode,
        frame: bytes | bytearray,
        signals: Mapping[str, int | Fraction],
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

        Raises:
            StateError: If the client is not initialized or no DBC is loaded
            ValidationError: If ``frame`` does not match ``dlc``, the DLC or
                CAN ID is invalid, no DBC message has the CAN ID, or a signal
                name is unknown
            InputBoundExceededError: If a value's numerator magnitude or
                denominator exceeds 2^128-1, the build's slots (``field``
                ``"signal value"``)
            TypeError: If a value is a ``bool`` or a ``float``
            ProtocolError: If the kernel refuses the update; ``code`` names the
                refusal, among them ``frame_value_out_of_range`` for a value
                outside the signal's declared ``[minimum, maximum]`` and
                ``frame_value_not_representable`` for a value no integer raw
                value scales to under the signal's factor and offset

        """
        expected_bytes = validate_payload_length(dlc, frame)
        validate_can_id(can_id, extended=extended)
        resolved = self._resolve_signal_indices(
            signals,
            can_id,
            "update_frame",
            extended=extended,
        )
        with self._ffi_lock:
            if self._backend is None or self._state is None:
                msg = "Client not initialized — use 'with' statement"
                raise StateError(msg)
            return bytearray(
                self._backend.update_frame_bin(
                    self._state,
                    can_id=can_id,
                    extended=extended,
                    dlc=dlc,
                    data=frame,
                    indices=resolved.indices,
                    values=resolved.values,
                    expected_bytes=expected_bytes,
                )
            )

    def build_frame(
        self,
        can_id: int,
        dlc: DLCCode,
        signals: Mapping[str, int | Fraction],
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

        Raises:
            StateError: If the client is not initialized or no DBC is loaded
            ValidationError: If the DLC or CAN ID is invalid, no DBC message has
                the CAN ID, or a signal name is unknown
            InputBoundExceededError: If a value's numerator magnitude or
                denominator exceeds 2^128-1, the build's slots (``field``
                ``"signal value"``)
            TypeError: If a value is a ``bool`` or a ``float``
            ProtocolError: If the kernel refuses the build; ``code`` names the
                refusal, among them ``frame_value_out_of_range`` for a value
                outside the signal's declared ``[minimum, maximum]`` and
                ``frame_value_not_representable`` for a value no integer raw
                value scales to under the signal's factor and offset

        """
        validate_can_id(can_id, extended=extended)
        resolved = self._resolve_signal_indices(
            signals,
            can_id,
            "build_frame",
            extended=extended,
        )
        with self._ffi_lock:
            if self._backend is None or self._state is None:
                msg = "Client not initialized — use 'with' statement"
                raise StateError(msg)
            return bytearray(
                self._backend.build_frame_bin(
                    self._state,
                    can_id=can_id,
                    extended=extended,
                    dlc=dlc,
                    indices=resolved.indices,
                    values=resolved.values,
                    expected_bytes=dlc_to_bytes(dlc),
                )
            )
