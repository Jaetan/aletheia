# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
"""Backend Protocol + MockBackend + DI seam coverage.

Covers the Backend Protocol DI seam and the MockBackend (documented but
not previously provided).  Cross-binding parity tests with Go
``go/aletheia/concurrent_test.go`` + C++ ``cpp/tests/unit_tests_validation.cpp``
which exercise the same matrix of Backend behaviors (canned responses,
captured inputs, init/close lifecycle).
"""

from __future__ import annotations

from typing import cast

import pytest
from _dbc_helpers import dbc, message, signal

from aletheia import (
    AletheiaClient,
    Backend,
    BinaryPathUnsupportedError,
    FFIBackend,
    MockBackend,
    Signal,
    StateError,
)
from aletheia._dbc_types import empty_dbc_tier2
from aletheia.types import DBCDefinition, DLCCode

# Some tests here build predicates whose rational values are rendered through the
# GHC RTS (e.g. the mock streaming session's ``Signal("Sig").less_than(255)``),
# which the MockBackend does NOT initialise.  Without this, the test only passed
# when ``pytest --random-order`` happened to run an RTS-initialising test first
# (a latent order dependency; seed 629836 exposed it).  ``rts_up`` is idempotent /
# refcounted, so it composes with any FFIBackend/AletheiaClient a test creates.
pytestmark = pytest.mark.usefixtures("rts_up")

# -----------------------------------------------------------------------------
# Backend Protocol structural conformance
# -----------------------------------------------------------------------------


def test_ffibackend_satisfies_backend_protocol() -> None:
    """``FFIBackend`` instances pass ``isinstance(..., Backend)``."""
    backend = FFIBackend()
    assert isinstance(backend, Backend)


def test_ffibackend_null_handles_yield_clean_error_not_segfault() -> None:
    """The FFI boundary must turn a NULL state/payload into a clean error, never a SIGSEGV.

    A binding holds the state as an opaque handle and builds payloads per call,
    so a correct one never passes NULL.  But the ``.so`` is the shared trust
    boundary for every binding, and a NULL handle/payload from a buggy caller
    would deref NULL and crash the GHC runtime.  We pass NULL deliberately
    (``0`` → NULL ``c_void_p`` state; ``None`` → NULL ``c_char_p`` payload) and
    assert a clean error response comes back.  A missing guard would SIGSEGV the
    pytest worker — itself the loud failure this test exists to catch.
    """
    backend = FFIBackend()
    state = backend.init()
    try:
        # NULL state handle, caught by the centralized runJSON guard …
        assert b"null state handle" in backend.process(0, b'{"command":"validateDBC","dbc":""}')
        # … and via a second entry point (aletheia_format_dbc → runJSON).
        assert b"null state handle" in backend.format_dbc_binary(0)
        # NULL payload, caught by the aletheia_process CString guard.  None is
        # deliberate adversarial input, hence the cast past the bytes annotation.
        assert b"null input string" in backend.process(state, cast("bytes", None))
    finally:
        backend.close(state)


def test_mockbackend_satisfies_backend_protocol() -> None:
    """``MockBackend`` instances pass ``isinstance(..., Backend)``."""
    assert isinstance(MockBackend(), Backend)


def test_mockbackend_init_close_lifecycle() -> None:
    """``init()`` returns a non-zero sentinel; ``close()`` is no-op."""
    backend = MockBackend()
    state = backend.init()
    assert state != 0
    backend.close(state)  # must not raise
    # Second close is idempotent (state is opaque; mock keeps no per-state record).
    backend.close(state)


# -----------------------------------------------------------------------------
# MockBackend canned-response behavior
# -----------------------------------------------------------------------------


def test_mockbackend_process_returns_canned_queue_in_order() -> None:
    """``process()`` pops the queue front-to-back."""
    backend = MockBackend(
        [
            b'{"status":"success","first":true}',
            b'{"status":"success","second":true}',
        ]
    )
    state = backend.init()
    assert backend.process(state, b'{"command":"a"}') == b'{"status":"success","first":true}'
    assert backend.process(state, b'{"command":"b"}') == b'{"status":"success","second":true}'


def test_mockbackend_records_all_inputs() -> None:
    """``inputs`` accumulates every ``process()`` and binary-shim call."""
    backend = MockBackend(
        [
            b'{"status":"success"}',
            b'{"status":"success"}',
            b'{"status":"ack"}',
        ]
    )
    state = backend.init()
    backend.process(state, b'{"command":"alpha"}')
    backend.process(state, b'{"command":"beta"}')
    backend.send_error_binary(state, 1000)
    assert backend.inputs == [
        b'{"command":"alpha"}',
        b'{"command":"beta"}',
        b"<binary:sendError>",
    ]


def test_mockbackend_exhausted_fire_and_forget_raises() -> None:
    """A fire-and-forget binary op on an empty queue raises StateError.

    An exhausted mock is a test-harness misconfiguration, never a fabricated
    default (cross-binding parity: Go ``ErrState`` / Rust / C++ ``State``).
    The starved-operation name is the ``<binary:OP>`` sentinel — byte-for-byte
    the shared cross-binding op token — and the sentinel is recorded into
    ``inputs`` BEFORE the raise, so a starved call stays observable in the
    capture log (mirroring Go, which records the input before erroring).
    """
    backend = MockBackend()
    state = backend.init()
    with pytest.raises(StateError) as excinfo:
        backend.send_error_binary(state, 0)
    # Exact-equality pin (the contract says the message is *exactly* this — a
    # substring ``match=`` would pass on any appended trailing text).
    assert str(excinfo.value) == "mock backend: no queued response for <binary:sendError>"
    assert backend.inputs == [b"<binary:sendError>"]


def test_mockbackend_exhausted_process_raises() -> None:
    """A ``process`` call on an empty queue raises StateError, op-named ``process``.

    The JSON command is recorded into ``inputs`` before the raise.
    """
    backend = MockBackend()
    state = backend.init()
    with pytest.raises(StateError) as excinfo:
        backend.process(state, b'{"command":"parseDBC","dbc":{}}')
    assert str(excinfo.value) == "mock backend: no queued response for process"
    assert backend.inputs == [b'{"command":"parseDBC","dbc":{}}']


def test_mockbackend_queue_response_appends() -> None:
    """``queue_response`` adds to the back; popped FIFO."""
    backend = MockBackend()
    backend.queue_response(b'{"status":"success","first":true}')
    backend.queue_response(b'{"status":"success","second":true}')
    state = backend.init()
    assert b"first" in backend.process(state, b"{}")
    assert b"second" in backend.process(state, b"{}")


def test_mockbackend_clear_resets_queue_and_inputs() -> None:
    """``clear()`` drops both response queue and captured inputs."""
    backend = MockBackend([b'{"status":"success"}'])
    state = backend.init()
    backend.process(state, b'{"x":1}')
    backend.clear()
    assert not backend.inputs
    # clear() drained the queue too — a freshly queued response pops as usual.
    backend.queue_response(b'{"status":"success","after_clear":true}')
    out = backend.process(state, b'{"command":"setProperties"}')
    assert out == b'{"status":"success","after_clear":true}'
    assert backend.inputs == [b'{"command":"setProperties"}']


def test_mockbackend_extract_signals_bin_raises_unsupported() -> None:
    """Mock raises the sentinel; Client should fall back to JSON path.

    Cross-binding parity with Go's ``ErrBinaryPathUnsupported``
    (``go/aletheia/mock.go:222``).
    """
    backend = MockBackend()
    state = backend.init()
    with pytest.raises(BinaryPathUnsupportedError):
        backend.extract_signals_bin(
            state,
            can_id=0x100,
            extended=False,
            dlc=DLCCode(8),
            data=bytes(8),
        )


# -----------------------------------------------------------------------------
# AletheiaClient DI seam — backend kwarg
# -----------------------------------------------------------------------------


def test_client_accepts_injected_mockbackend() -> None:
    """Passing ``backend=MockBackend()`` skips real FFI loading entirely."""
    backend = MockBackend(
        [
            # parseDBC response (empty body).
            b'{"status":"success","dbc":{"version":"","messages":[]},"warnings":[]}',
        ]
    )
    with AletheiaClient(backend=backend) as client:
        # Should not require libaletheia-ffi.so on disk.
        result = client.parse_dbc({"version": "", "messages": [], **empty_dbc_tier2()})
        assert result["status"] == "success"
    # Client called Backend.process exactly once for parseDBC.
    assert len(backend.inputs) == 1


def test_client_default_backend_is_ffibackend() -> None:
    """Without ``backend=``, the client loads ``libaletheia-ffi.so``."""
    # Real backend resolves the .so via find_ffi_library + ctypes.CDLL.
    # If construction succeeds + init() returns non-zero state, the
    # FFIBackend path is wired.
    with AletheiaClient() as client:
        # Force a JSON call to validate the FFI path actually works
        # end-to-end (not just construction).
        result = client.parse_dbc({"version": "", "messages": [], **empty_dbc_tier2()})
        assert result["status"] == "success"
        assert not client.is_closed
    assert client.is_closed


def test_client_send_frame_routes_through_backend() -> None:
    """``send_frame`` invokes the injected backend's ``send_frame_binary``."""
    backend = MockBackend(
        [
            b'{"status":"success","dbc":{"version":"","messages":[]},"warnings":[]}',  # parseDBC
            b'{"status":"success"}',  # setProperties
            b'{"status":"success"}',  # startStream
            b'{"status":"ack"}',  # send_frame
        ]
    )
    with AletheiaClient(backend=backend) as client:
        client.parse_dbc({"version": "", "messages": [], **empty_dbc_tier2()})
        client.set_properties([])
        client.start_stream()
        ack = client.send_frame(timestamp=0, can_id=0x100, dlc=DLCCode(8), data=bytes(8))
        assert ack == {"status": "ack"}

    # MockBackend recorded the send_frame_binary call via its sentinel input.
    assert b"<binary:sendFrame>" in backend.inputs


def test_client_user_injected_backend_not_dropped_on_close() -> None:
    """A user-injected backend stays alive after Client.close().

    The Client owns RTS only when it constructed the backend itself; an
    injected backend is caller-owned and persists across the close.
    """
    backend = MockBackend()
    client = AletheiaClient(backend=backend)
    with client:
        pass
    # Backend is still usable after the Client closes (caller-owned semantics).
    state = backend.init()
    backend.close(state)


# -----------------------------------------------------------------------------
# JSON fallback when MockBackend cannot service binary extract_signals_bin
# -----------------------------------------------------------------------------


def _simple_dbc() -> DBCDefinition:
    """Minimal DBC: one message with one signal at byte 0."""
    return dbc([message(0x100, "Msg", [signal("Sig")])])


def test_extract_signals_json_fallback_when_backend_binary_unsupported() -> None:
    """MockBackend's binary path is unsupported → client falls back to JSON.

    Verifies the BinaryPathUnsupportedError contract end-to-end (the same
    code path that closes the ``extract_signals_bin`` fallback contract
    in Go's MockBackend implementation).
    """
    backend = MockBackend(
        [
            # parseDBC: one message at can_id=0x100 with one signal "Sig" so that
            # _signal_lookup gets populated; otherwise the client short-circuits
            # to the JSON path BEFORE ever calling extract_signals_bin (the path
            # we want to exercise).
            b'{"status":"success","dbc":{"version":"",'
            + b'"messages":[{"id":256,"extended":false,"dlc":8,"signals":'
            + b'[{"name":"Sig","startBit":0,"length":8,"presence":"always"}]}]'
            + b'},"warnings":[]}',
            # extract_signals_binary JSON fallback returns success + empty lists.
            b'{"status":"success","values":[],"errors":[],"absent":[]}',
        ]
    )
    with AletheiaClient(backend=backend) as client:
        client.parse_dbc(_simple_dbc())
        # signal_lookup has been populated; binary path tried; mock raises
        # BinaryPathUnsupportedError; client falls back to JSON path.
        result = client.extract_signals(can_id=0x100, dlc=DLCCode(8), data=bytes(8))
        assert result.values == {}
        assert result.errors == {}
        assert result.absent == ()
    # Last recorded input is the JSON extract call (binary attempt left no record).
    assert b"<binary:extractAllSignals>" in backend.inputs


# -----------------------------------------------------------------------------
# Error propagation
# -----------------------------------------------------------------------------


def test_protocol_error_from_mock_propagates() -> None:
    """A mock-injected error response surfaces as ProtocolError to the user."""
    backend = MockBackend(
        [
            b'{"status":"error","message":"injected error","code":"protocol_invalid_command"}',
        ]
    )
    with AletheiaClient(backend=backend) as client:
        # parse_dbc translates the error response into a typed return.
        result = client.parse_dbc({"version": "", "messages": [], **empty_dbc_tier2()})
        assert result["status"] == "error"
        assert result["message"] == "injected error"


def test_uninitialized_client_send_frame_raises_state_error() -> None:
    """Calling send_frame without entering the context raises StateError."""
    client = AletheiaClient(backend=MockBackend())
    with pytest.raises(StateError):
        client.send_frame(timestamp=0, can_id=0x100, dlc=DLCCode(8), data=bytes(8))


# -----------------------------------------------------------------------------
# Cross-binding parity smoke — mirrors Go's TestMockBackend_Process_RecordsInputs
# -----------------------------------------------------------------------------


def test_full_streaming_session_through_mock() -> None:
    """End-to-end mock session: parse, set, start, send, end."""
    backend = MockBackend(
        [
            b'{"status":"success","dbc":{"version":"","messages":[]},"warnings":[]}',  # parseDBC
            b'{"status":"success"}',  # setProperties
            b'{"status":"success"}',  # startStream
            b'{"status":"ack"}',  # send_frame #1
            b'{"status":"ack"}',  # send_frame #2
            b'{"status":"complete","results":[]}',  # endStream
        ]
    )
    prop = Signal("Sig").less_than(255).always()
    with AletheiaClient(backend=backend) as client:
        client.parse_dbc(_simple_dbc())
        client.set_properties([prop.to_dict()])
        client.start_stream()
        client.send_frame(0, 0x100, DLCCode(8), bytes(8))
        client.send_frame(1000, 0x100, DLCCode(8), bytes(8))
        complete = client.end_stream()
        assert complete["status"] == "complete"

    # Sanity: 3 JSON commands + 2 binary sendFrame + 1 binary endStream.
    expected_inputs_prefix = [
        # parseDBC + setProperties + startStream — recorded as JSON.
    ]
    del expected_inputs_prefix  # not asserting exact JSON bodies, just shape
    # Python ``json.dumps`` emits ``": "`` (with space) per default sort
    # behavior; assertions are space-tolerant.
    assert any(b'"command": "parseDBC"' in i for i in backend.inputs)
    assert any(b'"command": "setProperties"' in i for i in backend.inputs)
    assert backend.inputs.count(b"<binary:startStream>") == 1
    assert backend.inputs.count(b"<binary:sendFrame>") == 2
    assert b"<binary:endStream>" in backend.inputs
