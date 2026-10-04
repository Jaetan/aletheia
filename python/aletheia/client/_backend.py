# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
"""The FFI boundary the client is given, so that a test can give it another.

The same boundary as Go's ``aletheia.Backend`` in ``go/aletheia/backend.go`` and
C++'s ``aletheia::IBackend`` in ``cpp/include/aletheia/backend.hpp``.

The protocol :class:`Backend` is what production code and tests both target,
structurally. :class:`FFIBackend` implements it over ``libaletheia-ffi.so``,
owning the loaded library, the reference to the GHC runtime and every ``ctypes``
call. :class:`MockBackend` implements it by replaying canned responses, for a
test that should not load the library, as Go's and C++'s mocks do.

A session's state is an ``int`` here, the address of what the kernel allocated,
and the client never looks inside it. Go passes the same address as an
``unsafe.Pointer``. C++ passes a ``BackendState``, a move-only handle that
closes the session when it goes out of scope, so that binding's call sites
neither hold nor release the address. :class:`FFIBackend` wraps the integer in
a ``ctypes.c_void_p`` at each call, and :class:`MockBackend` ignores it.
"""

from __future__ import annotations

import ctypes
from collections import deque
from typing import TYPE_CHECKING, Protocol, runtime_checkable

from aletheia.client._enrichment import set_renderer_lib
from aletheia.client._ffi import (
    AletheiaBuffer,
    AletheiaFrame,
    AletheiaSignalValues,
    AletheiaText,
    RTSState,
    check_abi_version,
    configure_ffi_signatures,
    find_ffi_library,
    parse_json_object,
)
from aletheia.client._types import (
    AletheiaError,
    FFIError,
    ProtocolError,
    StateError,
    encode_maybe_bool,
    validate_payload_length,
)
from aletheia.types import DLCCode

if TYPE_CHECKING:
    from pathlib import Path


class BinaryPathUnsupportedError(AletheiaError):
    """Raised by a Backend whose binary FFI methods are not supported.

    Cross-binding parity with Go ``ErrBinaryPathUnsupported`` and the
    fallback contract documented at ``go/aletheia/client.go:447``: when
    a Backend cannot service a binary-output method (e.g. MockBackend's
    :meth:`MockBackend.extract_signals_bin`), the Client catches this
    sentinel and falls back to the JSON-out path.
    """


@runtime_checkable
class Backend(Protocol):
    """FFI boundary abstraction — DI seam for testability.

    Production code uses :class:`FFIBackend`; tests use :class:`MockBackend`
    or a hand-rolled implementation.

    Cross-binding shape: 13 methods, mirroring Go's ``Backend`` interface
    and C++'s ``IBackend`` virtual surface.  See ``docs/FEATURE_MATRIX.yaml``
    row ``backend_di_seam`` for the matrix-level cross-binding parity record.

    All response-bytes-returning methods return ``bytes`` (not ``str``) so
    the streaming hot path's ``result_bytes in _ACK_RESPONSES`` membership
    test stays one C-level memcmp per frame.  Decoding to ``str`` and JSON
    parsing happen in the Client only when the fast path missed.
    """

    def init(self) -> int:
        """Create a new session and return an opaque state handle.

        Returns the raw ``void*`` address as ``int``; the Client passes
        it back unchanged on every subsequent call.
        """
        raise NotImplementedError

    def close(self, state: int) -> None:
        """Free per-session state and release any associated RTS reference."""
        raise NotImplementedError

    def process(self, state: int, input_bytes: bytes) -> bytes:
        """Send a JSON command and return the JSON response bytes."""
        raise NotImplementedError

    # send_frame_binary / build_frame_bin / update_frame_bin (here + on
    # FFIBackend / MockBackend) carry a per-line PLR0913 noqa: arg lists are
    # fixed by the binary-FFI wire contract + mirror Go/C++, and
    # send_frame_binary is the per-frame hot path.  PLR0913 stays active for
    # all other code.
    def send_frame_binary(  # pylint: disable=too-many-arguments  # noqa: PLR0913
        self,
        state: int,
        *,
        timestamp: int,
        can_id: int,
        extended: bool,
        dlc: int,
        data: bytes | bytearray,
        brs: bool | None,
        esi: bool | None,
    ) -> bytes:
        """Send a CAN frame via the binary FFI; returns the JSON response.

        BRS / ESI (CAN-FD ISO 11898-1:2015 §10.4.2 / §10.4.3) are
        pass-through metadata — not consumed by the Agda kernel.
        """
        raise NotImplementedError

    def send_error_binary(self, state: int, timestamp: int) -> bytes:
        """Send a CAN error event (no ID, no payload)."""
        raise NotImplementedError

    def send_remote_binary(
        self,
        state: int,
        *,
        timestamp: int,
        can_id: int,
        extended: bool,
    ) -> bytes:
        """Send a CAN remote frame event (ID, no payload)."""
        raise NotImplementedError

    def start_stream_binary(self, state: int) -> bytes:
        """Begin streaming mode."""
        raise NotImplementedError

    def end_stream_binary(self, state: int) -> bytes:
        """Finalize streaming and return verdicts."""
        raise NotImplementedError

    def format_dbc_binary(self, state: int) -> bytes:
        """Return the loaded DBC as JSON."""
        raise NotImplementedError

    def extract_signals_binary(  # pylint: disable=too-many-arguments
        self,
        state: int,
        *,
        can_id: int,
        extended: bool,
        dlc: int,
        data: bytes | bytearray,
    ) -> bytes:
        """Extract signals — JSON response on output (binding-friendly)."""
        raise NotImplementedError

    def build_frame_bin(  # pylint: disable=too-many-arguments  # noqa: PLR0913
        self,
        state: int,
        *,
        can_id: int,
        extended: bool,
        dlc: int,
        indices: tuple[int, ...],
        numerators: tuple[int, ...],
        denominators: tuple[int, ...],
        expected_bytes: int,
    ) -> bytes:
        """Build a CAN frame returning raw payload bytes (no JSON)."""
        raise NotImplementedError

    def update_frame_bin(  # pylint: disable=too-many-arguments  # noqa: PLR0913
        self,
        state: int,
        *,
        can_id: int,
        extended: bool,
        dlc: int,
        data: bytes | bytearray,
        indices: tuple[int, ...],
        numerators: tuple[int, ...],
        denominators: tuple[int, ...],
        expected_bytes: int,
    ) -> bytes:
        """Update specific signals in an existing frame returning raw payload bytes."""
        raise NotImplementedError

    def extract_signals_bin(  # pylint: disable=too-many-arguments
        self,
        state: int,
        *,
        can_id: int,
        extended: bool,
        dlc: int,
        data: bytes | bytearray,
    ) -> bytes:
        """Extract signals — packed binary on output (fast path).

        May raise :class:`BinaryPathUnsupportedError` if this backend does
        not implement the binary-out variant (e.g. MockBackend).  The
        Client falls back to :meth:`extract_signals_binary` when this
        exception is raised.
        """
        raise NotImplementedError


# ---------------------------------------------------------------------------
# Internal helpers shared by FFIBackend
# ---------------------------------------------------------------------------


def _decode_and_free_response(lib: ctypes.CDLL, ptr: int) -> bytes:
    """Read the C-string at ``ptr`` as ``bytes`` and free it.

    Common shape for every ``aletheia_*`` C function that returns a
    JSON response via a ``void*`` to a UTF-8 C string allocated by
    ``aletheia_free_str``-managed storage.
    """
    try:
        raw = ctypes.cast(ptr, ctypes.c_char_p).value
        if raw is None:
            msg = "FFI returned null pointer"
            raise ProtocolError(msg)
        return raw
    finally:
        lib.aletheia_free_str(ptr)


def _decode_out_err(
    lib: ctypes.CDLL,
    out: AletheiaBuffer,
    prefix: str,
) -> ProtocolError:
    """Decode a failed buffer's ``err`` envelope and return a :class:`ProtocolError`.

    The error is the JSON envelope every entry answers with
    (``{"status": "error", "code": …, "message": …}``): the kernel's typed
    refusal, or the shim's own (``ffi_validation_error``, a NULL pointer or a
    buffer too small).  The exception carries the envelope's ``code``.  Frees
    the ``err`` string.  The caller raises the returned exception (kept as a
    return value rather than ``NoReturn``-style raise so the call sites read
    linearly under pylint's ``too-many-statements`` budget).
    """
    err: int | None = out.err
    if err is None:
        return ProtocolError(f"{prefix}: Unknown error")
    try:
        envelope = parse_json_object(ctypes.string_at(err).decode("utf-8"))
    finally:
        lib.aletheia_free_str(err)
    code = envelope.get("code")
    message = envelope.get("message")
    if not isinstance(code, str) or not isinstance(message, str):
        return ProtocolError(f"{prefix}: malformed error envelope {envelope!r}")
    return ProtocolError(f"{prefix}: {message}", code=code)


def _payload_frame(
    *, can_id: int, extended: bool, dlc: int, data: bytes | bytearray
) -> AletheiaFrame:
    """Carry identifier, DLC and a copy of ``data`` in a frame with no timestamp or bus bits.

    Refuses a payload whose length is not the DLC's byte count, the one length
    the kernel accepts: the frame's ``data_len`` is a ``uint8_t`` and ctypes
    narrows silently, so a 264-byte payload would cross as 8 bytes.
    """
    _ = validate_payload_length(DLCCode(dlc), data)
    # `from_buffer_copy` is a single C-level memcpy; the frame keeps the
    # array alive for as long as the frame lives.
    data_array = (ctypes.c_uint8 * len(data)).from_buffer_copy(data)
    return AletheiaFrame(
        data=data_array,
        can_id=can_id,
        extended=1 if extended else 0,
        dlc=dlc,
        data_len=len(data),
    )


def _signal_values(
    indices: tuple[int, ...],
    numerators: tuple[int, ...],
    denominators: tuple[int, ...],
) -> AletheiaSignalValues:
    """Pack the parallel signal arrays into one ``struct aletheia_signal_values``."""
    n = len(indices)
    return AletheiaSignalValues(
        indices=(ctypes.c_uint32 * n)(*indices),
        numerators=(ctypes.c_int64 * n)(*numerators),
        denominators=(ctypes.c_int64 * n)(*denominators),
        count=n,
    )


# ---------------------------------------------------------------------------
# Production Backend
# ---------------------------------------------------------------------------


class FFIBackend:  # pylint: disable=too-many-public-methods
    """Production :class:`Backend` wrapping ``libaletheia-ffi.so`` via ctypes.

    Constructed eagerly: the shared library is ``dlopen``'d and the GHC
    RTS reference is acquired in :meth:`__init__`.  Mirrors C++
    ``aletheia::make_ffi_backend(path, rts_cores)`` (lib loaded at factory
    time) and Go ``aletheia.NewFFIBackend(opts...)`` (functional options
    pattern).

    Instances are reusable across multiple :class:`AletheiaClient` lifetimes
    — each ``init()`` returns a fresh state handle; each ``close(state)``
    frees just that handle's state without unloading the .so or releasing
    the RTS.  GHC's hs_init / hs_exit can only run once per process, so the
    RTS reference is held for the FFIBackend's lifetime; multiple FFIBackend
    instances share the module-level :class:`RTSState` refcount.
    """

    def __init__(
        self,
        *,
        rts_cores: int = 1,
        lib_path: Path | None = None,
    ) -> None:
        """Load ``libaletheia-ffi.so`` and acquire a GHC RTS reference.

        Args:
            rts_cores: GHC RTS capabilities (``-N`` flag). Use 1
                (default) for single-bus monitoring. Mismatch with an
                already-initialized process logs a warning; only the
                first call has effect.
            lib_path: Explicit path to ``libaletheia-ffi.so``.  When
                ``None``, :func:`find_ffi_library` resolves it from
                ``ALETHEIA_LIB`` / install config / build dir / cabal
                ``dist-newstyle``.

        Raises:
            FileNotFoundError: ``lib_path`` is None and no library found.
            PermissionError: Resolved library path is a symlink or
                group/world-writable (see :func:`._ffi._validate_lib_path`).

        """
        path = lib_path if lib_path is not None else find_ffi_library()
        self._lib: ctypes.CDLL = ctypes.CDLL(str(path))
        check_abi_version(self._lib)
        configure_ffi_signatures(self._lib)
        RTSState.acquire(self._lib, rts_cores)
        self._rts_cores = rts_cores
        # Register this library as the Rational renderer.  The renderer
        # loads its symbols lazily but NEVER initialises the RTS itself, so
        # this backend's RTS init (above) is what makes rendering work — a
        # caller that renders without any FFIBackend gets a vocal FFIError.
        set_renderer_lib(self._lib)

    @property
    def rts_cores(self) -> int:
        """RTS capabilities this backend was configured for."""
        return self._rts_cores

    def init(self) -> int:
        """Allocate a fresh Agda session and return the raw ``void*`` address."""
        raw = self._lib.aletheia_init()
        if not raw:
            msg = "aletheia_init() returned null — FFI initialization failed"
            raise FFIError(msg)
        return raw

    def close(self, state: int) -> None:
        """Free per-session state and decrement the RTS refcount."""
        # ``state == 0`` would be a null pointer; the Client guards against
        # double-close, but stay defensive in case a test calls close(0).
        if state:
            self._lib.aletheia_close(ctypes.c_void_p(state))
        RTSState.release()

    def process(self, state: int, input_bytes: bytes) -> bytes:
        """Send a JSON command string and return the JSON response bytes."""
        text = AletheiaText(input_bytes, len(input_bytes))
        result_ptr = self._lib.aletheia_process(ctypes.c_void_p(state), ctypes.byref(text))
        return _decode_and_free_response(self._lib, result_ptr)

    def send_frame_binary(  # pylint: disable=too-many-arguments,too-many-locals  # noqa: PLR0913
        self,
        state: int,
        *,
        timestamp: int,
        can_id: int,
        extended: bool,
        dlc: int,
        data: bytes | bytearray,
        brs: bool | None,
        esi: bool | None,
    ) -> bytes:
        """Send a CAN data frame via the binary FFI; returns the JSON response bytes."""
        # The exact length rule, for the reason `_payload_frame` gives.
        _ = validate_payload_length(DLCCode(dlc), data)
        # `from_buffer_copy` is a single C-level memcpy; the varargs form
        # `(c_uint8 * N)(*data)` does O(N) Python-level per-byte coercion.
        data_array = (ctypes.c_uint8 * len(data)).from_buffer_copy(data)
        brs_pres, brs_val = encode_maybe_bool(b=brs)
        esi_pres, esi_val = encode_maybe_bool(b=esi)
        frame = AletheiaFrame(
            timestamp=timestamp,
            data=data_array,
            can_id=can_id,
            extended=1 if extended else 0,
            dlc=dlc,
            data_len=len(data),
            brs_present=brs_pres,
            brs_value=brs_val,
            esi_present=esi_pres,
            esi_value=esi_val,
        )
        result_ptr = self._lib.aletheia_send_frame(ctypes.c_void_p(state), ctypes.byref(frame))
        return _decode_and_free_response(self._lib, result_ptr)

    def send_error_binary(self, state: int, timestamp: int) -> bytes:
        """Send a CAN error event; returns the JSON response bytes."""
        frame = AletheiaFrame(timestamp=timestamp)
        result_ptr = self._lib.aletheia_send_error(ctypes.c_void_p(state), ctypes.byref(frame))
        return _decode_and_free_response(self._lib, result_ptr)

    def send_remote_binary(
        self,
        state: int,
        *,
        timestamp: int,
        can_id: int,
        extended: bool,
    ) -> bytes:
        """Send a CAN remote frame; returns the JSON response bytes."""
        frame = AletheiaFrame(timestamp=timestamp, can_id=can_id, extended=1 if extended else 0)
        result_ptr = self._lib.aletheia_send_remote(ctypes.c_void_p(state), ctypes.byref(frame))
        return _decode_and_free_response(self._lib, result_ptr)

    def start_stream_binary(self, state: int) -> bytes:
        """Begin streaming mode; returns the JSON response bytes."""
        return _decode_and_free_response(
            self._lib,
            self._lib.aletheia_start_stream(ctypes.c_void_p(state)),
        )

    def end_stream_binary(self, state: int) -> bytes:
        """Finalize streaming; returns the JSON response bytes (per-property verdicts)."""
        return _decode_and_free_response(
            self._lib,
            self._lib.aletheia_end_stream(ctypes.c_void_p(state)),
        )

    def format_dbc_binary(self, state: int) -> bytes:
        """Return the loaded DBC as JSON bytes (no JSON on input)."""
        return _decode_and_free_response(
            self._lib,
            self._lib.aletheia_format_dbc(ctypes.c_void_p(state)),
        )

    def extract_signals_binary(  # pylint: disable=too-many-arguments
        self,
        state: int,
        *,
        can_id: int,
        extended: bool,
        dlc: int,
        data: bytes | bytearray,
    ) -> bytes:
        """Extract signals via the JSON-out path (no JSON on input)."""
        frame = _payload_frame(can_id=can_id, extended=extended, dlc=dlc, data=data)
        result_ptr = self._lib.aletheia_extract_signals(ctypes.c_void_p(state), ctypes.byref(frame))
        return _decode_and_free_response(self._lib, result_ptr)

    def build_frame_bin(  # pylint: disable=too-many-arguments,too-many-locals  # noqa: PLR0913
        self,
        state: int,
        *,
        can_id: int,
        extended: bool,
        dlc: int,
        indices: tuple[int, ...],
        numerators: tuple[int, ...],
        denominators: tuple[int, ...],
        expected_bytes: int,
    ) -> bytes:
        """Build a CAN frame from signal values; returns the packed payload bytes."""
        frame = AletheiaFrame(can_id=can_id, extended=1 if extended else 0, dlc=dlc)
        values = _signal_values(indices, numerators, denominators)
        out_buf = (ctypes.c_uint8 * expected_bytes)()
        out = AletheiaBuffer(data=out_buf, size=expected_bytes)
        status = self._lib.aletheia_build_frame_bin(
            ctypes.c_void_p(state),
            ctypes.byref(frame),
            ctypes.byref(values),
            ctypes.byref(out),
        )
        if status != 0:
            raise _decode_out_err(self._lib, out, "build_frame failed")
        return ctypes.string_at(out_buf, out.size)

    def update_frame_bin(  # pylint: disable=too-many-arguments,too-many-locals  # noqa: PLR0913
        self,
        state: int,
        *,
        can_id: int,
        extended: bool,
        dlc: int,
        data: bytes | bytearray,
        indices: tuple[int, ...],
        numerators: tuple[int, ...],
        denominators: tuple[int, ...],
        expected_bytes: int,
    ) -> bytes:
        """Update specified signals in ``data``; returns the new packed frame bytes."""
        frame = _payload_frame(can_id=can_id, extended=extended, dlc=dlc, data=data)
        values = _signal_values(indices, numerators, denominators)
        out_buf = (ctypes.c_uint8 * expected_bytes)()
        out = AletheiaBuffer(data=out_buf, size=expected_bytes)
        status = self._lib.aletheia_update_frame_bin(
            ctypes.c_void_p(state),
            ctypes.byref(frame),
            ctypes.byref(values),
            ctypes.byref(out),
        )
        if status != 0:
            raise _decode_out_err(self._lib, out, "update_frame failed")
        return ctypes.string_at(out_buf, out.size)

    def extract_signals_bin(  # pylint: disable=too-many-arguments
        self,
        state: int,
        *,
        can_id: int,
        extended: bool,
        dlc: int,
        data: bytes | bytearray,
    ) -> bytes:
        """Extract signals via the binary path; returns the packed-binary buffer."""
        frame = _payload_frame(can_id=can_id, extended=extended, dlc=dlc, data=data)
        out = AletheiaBuffer()
        status = self._lib.aletheia_extract_signals_bin(
            ctypes.c_void_p(state),
            ctypes.byref(frame),
            ctypes.byref(out),
        )
        if status != 0:
            raise _decode_out_err(self._lib, out, "extract_signals failed")
        try:
            return ctypes.string_at(out.data, out.size)
        finally:
            self._lib.aletheia_free_buf(out.data)


# ---------------------------------------------------------------------------
# Mock Backend
# ---------------------------------------------------------------------------


_MOCK_SENTINEL_STATE: int = 0xDEADBEEF  # Non-null sentinel; mock ignores state value.


class MockBackend:  # pylint: disable=too-many-public-methods
    r"""In-memory :class:`Backend` replaying canned JSON responses.

    Cross-binding parity with Go ``aletheia.MockBackend`` (mock.go) and
    C++ ``aletheia::MockBackend`` (``cpp/src/detail/mock_backend.hpp``).
    Tracks ``FEATURE_MATRIX.yaml`` row ``mock_backend`` for the Python
    binding.

    Usage::

        from aletheia import AletheiaClient, MockBackend

        backend = MockBackend([
            b'{"status":"success","dbc":{...},"warnings":[]}',  # parse_dbc
            b'{"status":"ack"}',                                # send_frame
        ])
        with AletheiaClient(backend=backend) as client:
            client.parse_dbc(dbc)
            client.send_frame(0, 0x100, 0, b"\x00")

        assert len(backend.inputs) == 2

    Concurrency: instances are NOT thread-safe.  Each test should
    construct its own instance.  Cross-binding note: Go's MockBackend
    serializes through a Mutex; Python's stays GIL-protected for simple
    state mutations (deque + counter).  Tests requiring cross-thread mock
    coordination should layer a lock externally.
    """

    def __init__(self, responses: list[bytes] | None = None) -> None:
        """Pre-load the canned response queue.

        Args:
            responses: JSON response bytes returned one per call.  Empty
                / None queues an empty deque.  A call that finds the queue
                empty raises :class:`StateError` (an exhausted mock is a
                test-harness misconfiguration, never a fabricated default)
                — so every test must enqueue exactly one response per
                expected backend call.  Cross-binding parity: Go
                ``ErrState`` / Rust ``Error`` / C++ ``ErrorKind::State`` all
                error on an exhausted mock queue rather than inventing a
                response.

        """
        self._responses: deque[bytes] = deque(responses or [])
        self._inputs: list[bytes] = []

    @property
    def inputs(self) -> list[bytes]:
        """All JSON command bytes the Client has sent through this backend.

        Recorded by :meth:`process` and the binary-shim methods that
        marshal a JSON command before delegating.  Returns the live list
        — callers may snapshot via ``list(backend.inputs)`` if mutation
        between assertions is a concern.
        """
        return self._inputs

    def queue_response(self, response: bytes) -> None:
        """Append a canned response to the back of the queue."""
        self._responses.append(response)

    def clear(self) -> None:
        """Reset both the response queue and the recorded inputs."""
        self._responses.clear()
        self._inputs.clear()

    def _record_and_pop(self, input_bytes: bytes, op: str | None = None) -> bytes:
        """Record *input_bytes*, then pop and return the next queued response.

        Raises :class:`StateError` on an exhausted queue — a MockBackend
        that runs out of canned responses is a test-harness
        misconfiguration, NEVER a fabricated default that would let an
        under-provisioned test pass silently (cross-binding parity: Go
        ``ErrState`` / Rust ``Error`` / C++ ``ErrorKind::State``).  The
        input is appended to :attr:`inputs` BEFORE the raise, so the
        capture log stays populated on the starved call (mirroring Go,
        which records the input before erroring).

        The starved-operation name in the message is *op* when given (the
        JSON path passes ``"process"``); otherwise it defaults to the
        decoded *input_bytes*, which for every binary shim is the
        ``<binary:OP>`` sentinel it records — yielding a message byte-for-byte
        identical to the peer bindings.
        """
        self._inputs.append(input_bytes)
        if not self._responses:
            starved = op if op is not None else input_bytes.decode("utf-8", "replace")
            msg = f"mock backend: no queued response for {starved}"
            raise StateError(msg)
        return self._responses.popleft()

    def init(self) -> int:
        """Return a non-zero sentinel state handle (mock keeps no per-state record)."""
        return _MOCK_SENTINEL_STATE

    def close(self, state: int) -> None:
        """No-op — mock does not retain per-session state."""
        del state

    def process(self, state: int, input_bytes: bytes) -> bytes:
        """Record the JSON input and return the next queued response."""
        del state
        return self._record_and_pop(input_bytes, "process")

    def send_frame_binary(  # pylint: disable=too-many-arguments  # noqa: PLR0913
        self,
        state: int,
        *,
        timestamp: int,
        can_id: int,
        extended: bool,
        dlc: int,
        data: bytes | bytearray,
        brs: bool | None,
        esi: bool | None,
    ) -> bytes:
        """Record a ``<binary:sendFrame>`` sentinel; return the queued response."""
        del state, timestamp, can_id, extended, dlc, data, brs, esi
        return self._record_and_pop(b"<binary:sendFrame>")

    def send_error_binary(self, state: int, timestamp: int) -> bytes:
        """Record a ``<binary:sendError>`` sentinel; return the queued response."""
        del state, timestamp
        return self._record_and_pop(b"<binary:sendError>")

    def send_remote_binary(
        self,
        state: int,
        *,
        timestamp: int,
        can_id: int,
        extended: bool,
    ) -> bytes:
        """Record a ``<binary:sendRemote>`` sentinel; return the queued response."""
        del state, timestamp, can_id, extended
        return self._record_and_pop(b"<binary:sendRemote>")

    def start_stream_binary(self, state: int) -> bytes:
        """Record a ``<binary:startStream>`` sentinel; return the queued response."""
        del state
        return self._record_and_pop(b"<binary:startStream>")

    def end_stream_binary(self, state: int) -> bytes:
        """Record a ``<binary:endStream>`` sentinel; return the queued response."""
        del state
        return self._record_and_pop(b"<binary:endStream>")

    def format_dbc_binary(self, state: int) -> bytes:
        """Record a ``<binary:formatDBC>`` sentinel; return the queued response."""
        del state
        return self._record_and_pop(b"<binary:formatDBC>")

    def extract_signals_binary(  # pylint: disable=too-many-arguments
        self,
        state: int,
        *,
        can_id: int,
        extended: bool,
        dlc: int,
        data: bytes | bytearray,
    ) -> bytes:
        """Record a ``<binary:extractAllSignals>`` sentinel; return the queued response."""
        del state, can_id, extended, dlc, data
        return self._record_and_pop(b"<binary:extractAllSignals>")

    def build_frame_bin(  # pylint: disable=too-many-arguments  # noqa: PLR0913
        self,
        state: int,
        *,
        can_id: int,
        extended: bool,
        dlc: int,
        indices: tuple[int, ...],
        numerators: tuple[int, ...],
        denominators: tuple[int, ...],
        expected_bytes: int,
    ) -> bytes:
        """Record a ``<binary:buildFrameBin>`` sentinel; return the queued packed frame bytes."""
        del state, can_id, extended, dlc, indices, numerators, denominators, expected_bytes
        # The next queued response is treated as the packed frame bytes.
        return self._record_and_pop(b"<binary:buildFrameBin>")

    def update_frame_bin(  # pylint: disable=too-many-arguments  # noqa: PLR0913
        self,
        state: int,
        *,
        can_id: int,
        extended: bool,
        dlc: int,
        data: bytes | bytearray,
        indices: tuple[int, ...],
        numerators: tuple[int, ...],
        denominators: tuple[int, ...],
        expected_bytes: int,
    ) -> bytes:
        """Record a ``<binary:updateFrameBin>`` sentinel; return the queued packed frame bytes."""
        del state, can_id, extended, dlc, data, indices, numerators, denominators, expected_bytes
        return self._record_and_pop(b"<binary:updateFrameBin>")

    def extract_signals_bin(  # pylint: disable=too-many-arguments
        self,
        state: int,
        *,
        can_id: int,
        extended: bool,
        dlc: int,
        data: bytes | bytearray,
    ) -> bytes:
        """Raise :class:`BinaryPathUnsupportedError` to trigger JSON fallback.

        Mirrors Go ``MockBackend.ExtractSignalsBin`` returning
        ``ErrBinaryPathUnsupported`` (``go/aletheia/mock.go:222``); the
        Client catches the sentinel and falls back to JSON.
        """
        del state, can_id, extended, dlc, data
        raise BinaryPathUnsupportedError(
            "MockBackend does not implement the binary extraction path;"
            + " Client should fall back to JSON via extract_signals_binary."
        )


__all__ = [
    "Backend",
    "BinaryPathUnsupportedError",
    "FFIBackend",
    "MockBackend",
]
