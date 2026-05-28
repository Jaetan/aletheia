"""Backend Protocol — FFI-boundary DI seam for the Aletheia client.

Mirrors Go ``aletheia.Backend`` (``go/aletheia/backend.go``) and C++
``aletheia::IBackend`` (``cpp/include/aletheia/backend.hpp``) for
cross-binding parity at the FFI boundary.

Three implementations live here:

* :class:`Backend` — the Protocol (structural typing) production code and
  tests both target.
* :class:`FFIBackend` — production wrapper around ``libaletheia-ffi.so``;
  owns the loaded shared library, the GHC RTS reference, and every
  ``ctypes`` call.
* :class:`MockBackend` — canned-response replay for tests that should not
  load the .so (cross-binding parity with Go ``MockBackend`` /
  C++ ``aletheia::MockBackend`` at ``cpp/src/detail/mock_backend.hpp``).

The state handle is ``int`` (raw ``void*`` address as integer) — opaque
to the client, matching Go ``unsafe.Pointer`` and C++ ``void*`` opacity.
``FFIBackend`` converts to ``ctypes.c_void_p(state)`` at each FFI call
boundary; ``MockBackend`` ignores it entirely.
"""

from __future__ import annotations

import ctypes
from collections import deque
from typing import TYPE_CHECKING, Protocol, runtime_checkable

from aletheia.client._enrichment import set_renderer_lib
from aletheia.client._ffi import RTSState, configure_ffi_signatures, find_ffi_library
from aletheia.client._types import AletheiaError, FFIError, ProtocolError, encode_maybe_bool

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
    out_err: ctypes.c_char_p,
    prefix: str,
) -> ProtocolError:
    """Decode an ``out_err`` C-string and return a :class:`ProtocolError`.

    Free's the ``out_err`` buffer.  The caller raises the returned
    exception (kept as a return value rather than ``NoReturn``-style raise
    so the call sites read linearly under pylint's ``too-many-statements``
    budget).
    """
    # ctypes.cast narrows to bytes|None correctly for pylint (direct
    # out_err.value flags .decode as no-member).
    raw_err = ctypes.cast(out_err, ctypes.c_char_p).value
    if raw_err is None:
        return ProtocolError(f"{prefix}: Unknown error")
    err_msg = raw_err.decode("utf-8")
    lib.aletheia_free_str(out_err)
    return ProtocolError(f"{prefix}: {err_msg}")


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
        configure_ffi_signatures(self._lib)
        RTSState.acquire(self._lib, rts_cores)
        self._rts_cores = rts_cores
        # Register this library as the Rational renderer.  The renderer
        # module also lazy-loads on demand for callers that bypass
        # FFIBackend, so this registration is an eager optimisation rather
        # than a strict requirement.
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
        result_ptr = self._lib.aletheia_process(ctypes.c_void_p(state), input_bytes)
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
        # `from_buffer_copy` is a single C-level memcpy; the varargs form
        # `(c_uint8 * N)(*data)` does O(N) Python-level per-byte coercion.
        data_array = (ctypes.c_uint8 * len(data)).from_buffer_copy(data)
        brs_pres, brs_val = encode_maybe_bool(b=brs)
        esi_pres, esi_val = encode_maybe_bool(b=esi)
        result_ptr = self._lib.aletheia_send_frame(
            ctypes.c_void_p(state),
            ctypes.c_uint64(timestamp),
            ctypes.c_uint32(can_id),
            ctypes.c_uint8(1 if extended else 0),
            ctypes.c_uint8(dlc),
            data_array,
            ctypes.c_uint8(len(data)),
            ctypes.c_uint8(brs_pres),
            ctypes.c_uint8(brs_val),
            ctypes.c_uint8(esi_pres),
            ctypes.c_uint8(esi_val),
        )
        return _decode_and_free_response(self._lib, result_ptr)

    def send_error_binary(self, state: int, timestamp: int) -> bytes:
        """Send a CAN error event; returns the JSON response bytes."""
        result_ptr = self._lib.aletheia_send_error(
            ctypes.c_void_p(state),
            ctypes.c_uint64(timestamp),
        )
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
        result_ptr = self._lib.aletheia_send_remote(
            ctypes.c_void_p(state),
            ctypes.c_uint64(timestamp),
            ctypes.c_uint32(can_id),
            ctypes.c_uint8(1 if extended else 0),
        )
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
        data_array = (ctypes.c_uint8 * len(data)).from_buffer_copy(data)
        result_ptr = self._lib.aletheia_extract_signals(
            ctypes.c_void_p(state),
            ctypes.c_uint32(can_id),
            ctypes.c_uint8(1 if extended else 0),
            ctypes.c_uint8(dlc),
            data_array,
            ctypes.c_uint8(len(data)),
        )
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
        out_buf = (ctypes.c_uint8 * expected_bytes)()
        out_err = ctypes.c_char_p()
        n = len(indices)
        status = self._lib.aletheia_build_frame_bin(
            ctypes.c_void_p(state),
            ctypes.c_uint32(can_id),
            ctypes.c_uint8(1 if extended else 0),
            ctypes.c_uint8(dlc),
            ctypes.c_uint32(n),
            (ctypes.c_uint32 * n)(*indices),
            (ctypes.c_int64 * n)(*numerators),
            (ctypes.c_int64 * n)(*denominators),
            out_buf,
            ctypes.byref(out_err),
        )
        if status != 0:
            raise _decode_out_err(self._lib, out_err, "build_frame failed")
        return bytes(out_buf)

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
        frame_array = (ctypes.c_uint8 * len(data)).from_buffer_copy(data)
        out_buf = (ctypes.c_uint8 * expected_bytes)()
        out_err = ctypes.c_char_p()
        n = len(indices)
        status = self._lib.aletheia_update_frame_bin(
            ctypes.c_void_p(state),
            ctypes.c_uint32(can_id),
            ctypes.c_uint8(1 if extended else 0),
            ctypes.c_uint8(dlc),
            frame_array,
            ctypes.c_uint8(len(data)),
            ctypes.c_uint32(n),
            (ctypes.c_uint32 * n)(*indices),
            (ctypes.c_int64 * n)(*numerators),
            (ctypes.c_int64 * n)(*denominators),
            out_buf,
            ctypes.byref(out_err),
        )
        if status != 0:
            raise _decode_out_err(self._lib, out_err, "update_frame failed")
        return bytes(out_buf)

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
        data_array = (ctypes.c_uint8 * len(data)).from_buffer_copy(data)
        out_buf = ctypes.POINTER(ctypes.c_uint8)()
        out_size = ctypes.c_uint32()
        out_err = ctypes.c_char_p()
        status = self._lib.aletheia_extract_signals_bin(
            ctypes.c_void_p(state),
            ctypes.c_uint32(can_id),
            ctypes.c_uint8(1 if extended else 0),
            ctypes.c_uint8(dlc),
            data_array,
            ctypes.c_uint8(len(data)),
            ctypes.byref(out_buf),
            ctypes.byref(out_size),
            ctypes.byref(out_err),
        )
        if status != 0:
            raise _decode_out_err(self._lib, out_err, "extract_signals failed")
        try:
            return bytes(
                ctypes.cast(
                    out_buf,
                    ctypes.POINTER(ctypes.c_uint8 * out_size.value),
                ).contents
            )
        finally:
            self._lib.aletheia_free_buf(out_buf)


# ---------------------------------------------------------------------------
# Mock Backend
# ---------------------------------------------------------------------------


# Default ack JSON for unsolicited "fire-and-forget" mock calls.  Mirrors
# the Go MockBackend default at ``go/aletheia/mock.go`` and the C++ default
# at ``cpp/src/detail/mock_backend.hpp:62``.
_MOCK_ACK_RESPONSE: bytes = b'{"status":"ack"}'
_MOCK_SUCCESS_RESPONSE: bytes = b'{"status":"success"}'

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
                / None queues an empty deque; calls past the queue length
                fall back to :func:`default_response` (``{"status":"ack"}``
                for fire-and-forget endpoints, ``{"status":"success"}``
                otherwise) so simple smoke tests work without explicit
                priming.  Tests asserting on exact response shapes should
                enqueue every expected call.

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

    # Marker substrings identifying fire-and-forget calls (JSON commands or
    # binary-shim sentinels) that should default to ``{"status":"ack"}``
    # rather than ``{"status":"success"}``.
    _ACK_DEFAULT_MARKERS: tuple[bytes, ...] = (
        b'"command":"sendFrame"',
        b'"command":"sendError"',
        b'"command":"sendRemote"',
        b"<binary:sendFrame>",
        b"<binary:sendError>",
        b"<binary:sendRemote>",
    )

    @classmethod
    def default_response(cls, input_bytes: bytes) -> bytes:
        """Return the default response when the queue is empty.

        Mirrors C++ ``MockBackend::process`` default: fire-and-forget
        commands (``sendFrame`` / ``sendError`` / ``sendRemote`` — JSON
        path or binary sentinel) return ``{"status":"ack"}``; everything
        else returns ``{"status":"success"}``.
        """
        if any(m in input_bytes for m in cls._ACK_DEFAULT_MARKERS):
            return _MOCK_ACK_RESPONSE
        return _MOCK_SUCCESS_RESPONSE

    def _pop_or_default(self, input_bytes: bytes) -> bytes:
        """Record the input then return the next queued response, or the default."""
        self._inputs.append(input_bytes)
        if self._responses:
            return self._responses.popleft()
        return self.default_response(input_bytes)

    def init(self) -> int:
        """Return a non-zero sentinel state handle (mock keeps no per-state record)."""
        return _MOCK_SENTINEL_STATE

    def close(self, state: int) -> None:
        """No-op — mock does not retain per-session state."""
        del state

    def process(self, state: int, input_bytes: bytes) -> bytes:
        """Record the JSON input and return the next queued (or default) response."""
        del state
        return self._pop_or_default(input_bytes)

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
        """Record a ``<binary:sendFrame>`` sentinel; return queued or default-ack."""
        del state, timestamp, can_id, extended, dlc, data, brs, esi
        return self._pop_or_default(b"<binary:sendFrame>")

    def send_error_binary(self, state: int, timestamp: int) -> bytes:
        """Record a ``<binary:sendError>`` sentinel; return queued or default-ack."""
        del state, timestamp
        return self._pop_or_default(b"<binary:sendError>")

    def send_remote_binary(
        self,
        state: int,
        *,
        timestamp: int,
        can_id: int,
        extended: bool,
    ) -> bytes:
        """Record a ``<binary:sendRemote>`` sentinel; return queued or default-ack."""
        del state, timestamp, can_id, extended
        return self._pop_or_default(b"<binary:sendRemote>")

    def start_stream_binary(self, state: int) -> bytes:
        """Record a ``<binary:startStream>`` sentinel; return queued or success."""
        del state
        return self._pop_or_default(b"<binary:startStream>")

    def end_stream_binary(self, state: int) -> bytes:
        """Record a ``<binary:endStream>`` sentinel; return queued or success."""
        del state
        return self._pop_or_default(b"<binary:endStream>")

    def format_dbc_binary(self, state: int) -> bytes:
        """Record a ``<binary:formatDBC>`` sentinel; return queued or success."""
        del state
        return self._pop_or_default(b"<binary:formatDBC>")

    def extract_signals_binary(  # pylint: disable=too-many-arguments
        self,
        state: int,
        *,
        can_id: int,
        extended: bool,
        dlc: int,
        data: bytes | bytearray,
    ) -> bytes:
        """Record a ``<binary:extractAllSignals>`` sentinel; return queued or success."""
        del state, can_id, extended, dlc, data
        return self._pop_or_default(b"<binary:extractAllSignals>")

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
        """Pop a queued frame bytes; zero-fill to ``expected_bytes`` if empty."""
        del state, can_id, extended, dlc, indices, numerators, denominators
        # The next queued response is treated as the packed frame bytes;
        # without a queued response, zero-fill to expected_bytes so the
        # downstream length validation in update_frame passes.
        self._inputs.append(b"<binary:buildFrameBin>")
        if self._responses:
            return self._responses.popleft()
        return bytes(expected_bytes)

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
        """Pop a queued frame bytes; zero-fill to ``expected_bytes`` if empty."""
        del state, can_id, extended, dlc, data, indices, numerators, denominators
        self._inputs.append(b"<binary:updateFrameBin>")
        if self._responses:
            return self._responses.popleft()
        return bytes(expected_bytes)

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
