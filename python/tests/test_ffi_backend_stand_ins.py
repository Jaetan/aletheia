# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
"""What :class:`FFIBackend` hands the kernel's entries, and what it makes of their answers.

The real kernel reads a frame's extended byte only as zero or not and
acknowledges a close or the release of a string or a buffer without reading
any, so these tests run on the recording stand-in: it quotes what each frame
entry is handed, keeps the state its last close was handed and counts the
strings and buffers it releases. The null stand-in answers a null session and
a null string, and fails each binary entry without an error envelope. Every
test gives the process a runtime latch nothing has set (``unstarted``), so the
stand-in's backend latches its own library, restored after the test. The
stand-ins are the ones ``cabal run shake -- build`` makes beside the library.
"""

from __future__ import annotations

import ctypes
from fractions import Fraction
from typing import TYPE_CHECKING, NamedTuple, NewType

import pytest
from _stand_in import StandInName, keeping, stand_in_kernel

from aletheia import AletheiaError, FFIBackend, FFIError, ProtocolError
from aletheia.client._ffi import take_error_envelope

if TYPE_CHECKING:
    from collections.abc import Callable

    from aletheia.types import JSONValue

pytestmark = pytest.mark.usefixtures("unstarted")

_RECORDING = StandInName("recording_kernel")
_NULL = StandInName("null_kernel")

# The recording stand-in's quote of what an entry was handed.
Quote = NewType("Quote", str)

# The error envelope a string entry answers, as its bytes.
Envelope = NewType("Envelope", bytes)

# A count the recording stand-in keeps.
Count = NewType("Count", int)

# Every frame below carries this timestamp and identifier, 0x123, and a DLC-8 payload.
_TIMESTAMP = 1000
_CAN_ID = 0x123
_DLC = 8
_PAYLOAD = bytes(_DLC)


def _refused(quote: Quote) -> Envelope:
    """Return the envelope the recording stand-in answers a string entry with."""
    return Envelope(f'{{"status":"error","code":"recording_kernel","message":"{quote}"}}'.encode())


def _taken(quote: Quote) -> JSONValue:
    """Return the envelope the recording stand-in answers a structure entry with, as read."""
    return {"status": "error", "code": "recording_kernel", "message": quote}


# The refusal of the recording stand-in's code, which no error code names.
_NO_ERROR_CODE = 'reply code: expected an error code, got "recording_kernel"'


def _recording() -> FFIBackend:
    return FFIBackend(lib_path=stand_in_kernel(_RECORDING))


def _kept() -> ctypes.CDLL:
    """Open the recording stand-in again, the backend's own mapping, to read what it kept."""
    return ctypes.CDLL(str(stand_in_kernel(_RECORDING)))


def test_a_null_session_is_an_ffi_error() -> None:
    """A session the library answers as null is refused as an ``FFIError`` with no code."""
    backend = FFIBackend(lib_path=stand_in_kernel(_NULL))
    with pytest.raises(FFIError) as refused:
        _ = backend.init()
    assert (str(refused.value), refused.value.code) == ("aletheia_init returned null", None)


def test_a_close_hands_the_library_the_state_its_open_answered() -> None:
    """The state a close hands the library is the one the session's open answered."""
    backend = _recording()
    state = backend.init()
    backend.close(state)
    last_closed = _kept().aletheia_test_last_closed
    last_closed.restype = ctypes.c_void_p
    assert last_closed() == state


class _DataFrame(NamedTuple):
    """A data frame's extended bit and CAN-FD bus bits, and the stand-in's quote of its frame."""

    extended: bool
    brs: bool | None
    esi: bool | None
    quote: Quote


_DATA_FRAMES = [
    _DataFrame(
        extended=True,
        brs=True,
        esi=True,
        quote=Quote("send_frame ts=1000 id=291 extended=1 dlc=8 len=8 brs=1/1 esi=1/1"),
    ),
    _DataFrame(
        extended=False,
        brs=False,
        esi=None,
        quote=Quote("send_frame ts=1000 id=291 extended=0 dlc=8 len=8 brs=1/0 esi=0/0"),
    ),
    _DataFrame(
        extended=False,
        brs=None,
        esi=False,
        quote=Quote("send_frame ts=1000 id=291 extended=0 dlc=8 len=8 brs=0/0 esi=1/0"),
    ),
]


@pytest.mark.parametrize(
    "frame", _DATA_FRAMES, ids=["extended, both bits set", "BRS clear", "ESI clear"]
)
def test_a_data_frame_reaches_the_entry_whole(frame: _DataFrame) -> None:
    """A data frame's entry is handed its timestamp, identifier, bits, DLC and length.

    Each bus bit crosses as a byte pair, present then value, present 0 for a
    bit the frame does not carry.
    """
    backend = _recording()
    answered = backend.send_frame_binary(
        backend.init(),
        timestamp=_TIMESTAMP,
        can_id=_CAN_ID,
        extended=frame.extended,
        dlc=_DLC,
        data=_PAYLOAD,
        brs=frame.brs,
        esi=frame.esi,
    )
    assert answered == _refused(frame.quote)


@pytest.mark.parametrize(
    ("extended", "quote"),
    [
        (True, Quote("send_remote ts=1000 id=291 extended=1")),
        (False, Quote("send_remote ts=1000 id=291 extended=0")),
    ],
    ids=["extended", "standard"],
)
def test_a_remote_frame_reaches_the_entry_whole(*, extended: bool, quote: Quote) -> None:
    """A remote frame's entry is handed its timestamp, its identifier and its extended bit."""
    backend = _recording()
    answered = backend.send_remote_binary(
        backend.init(), timestamp=_TIMESTAMP, can_id=_CAN_ID, extended=extended
    )
    assert answered == _refused(quote)


def test_an_extraction_hands_the_entry_the_frame_whole() -> None:
    """The extraction answering JSON is handed the frame's identifier, bit, DLC and length."""
    backend = _recording()
    answered = backend.extract_signals_binary(
        backend.init(), can_id=_CAN_ID, extended=True, dlc=_DLC, data=_PAYLOAD
    )
    assert answered == _refused(Quote("extract_signals id=291 extended=1 dlc=8 len=8"))


def test_a_build_hands_the_entry_the_frame_whole(monkeypatch: pytest.MonkeyPatch) -> None:
    """A build is handed the frame's identifier, extended bit and DLC, and no payload.

    The stand-in's envelope is read as the backend took it, before refusing its code.
    """
    backend = _recording()
    take, taken = keeping(take_error_envelope)
    monkeypatch.setattr("aletheia.client._backend.take_error_envelope", take)
    with pytest.raises(ProtocolError) as refused:
        _ = backend.build_frame_bin(
            backend.init(),
            can_id=_CAN_ID,
            extended=True,
            dlc=_DLC,
            indices=(0,),
            values=(Fraction(1),),
            expected_bytes=_DLC,
        )
    assert (str(refused.value), refused.value.code) == (_NO_ERROR_CODE, None)
    assert taken == [_taken(Quote("build_frame_bin id=291 extended=1 dlc=8 len=0"))]


def test_an_update_hands_the_entry_the_frame_whole(monkeypatch: pytest.MonkeyPatch) -> None:
    """An update is handed the frame's identifier, extended bit, DLC and payload length.

    The stand-in's envelope is read as the backend took it, before refusing its code.
    """
    backend = _recording()
    take, taken = keeping(take_error_envelope)
    monkeypatch.setattr("aletheia.client._backend.take_error_envelope", take)
    with pytest.raises(ProtocolError) as refused:
        _ = backend.update_frame_bin(
            backend.init(),
            can_id=_CAN_ID,
            extended=True,
            dlc=_DLC,
            data=_PAYLOAD,
            indices=(0,),
            values=(Fraction(1),),
            expected_bytes=_DLC,
        )
    assert (str(refused.value), refused.value.code) == (_NO_ERROR_CODE, None)
    assert taken == [_taken(Quote("update_frame_bin id=291 extended=1 dlc=8 len=8"))]


def test_a_binary_extraction_answers_its_buffer_and_releases_it() -> None:
    """The binary extraction answers the bytes of the buffer it was handed, then releases it.

    The recording stand-in's buffer holds its quote of the frame, and it counts
    each buffer released to it.
    """
    backend = _recording()
    state = backend.init()
    released = _kept().aletheia_test_buffer_free_count
    before = Count(released())
    answered = backend.extract_signals_bin(
        state, can_id=_CAN_ID, extended=True, dlc=_DLC, data=_PAYLOAD
    )
    assert (answered, Count(released())) == (
        b"extract_signals_bin id=291 extended=1 dlc=8 len=8",
        Count(before + 1),
    )


def test_a_binary_entry_failing_without_an_envelope_is_a_protocol_error_naming_it() -> None:
    """A binary entry failing with no envelope is a ``ProtocolError`` with no code, naming it."""
    backend = FFIBackend(lib_path=stand_in_kernel(_NULL))
    # The null stand-in ignores the state, as it answers every session as null.
    state = 0
    with pytest.raises(ProtocolError) as built:
        _ = backend.build_frame_bin(
            state,
            can_id=_CAN_ID,
            extended=False,
            dlc=_DLC,
            indices=(0,),
            values=(Fraction(1),),
            expected_bytes=_DLC,
        )
    with pytest.raises(ProtocolError) as updated:
        _ = backend.update_frame_bin(
            state,
            can_id=_CAN_ID,
            extended=False,
            dlc=_DLC,
            data=_PAYLOAD,
            indices=(0,),
            values=(Fraction(1),),
            expected_bytes=_DLC,
        )
    with pytest.raises(ProtocolError) as extracted:
        _ = backend.extract_signals_bin(
            state, can_id=_CAN_ID, extended=False, dlc=_DLC, data=_PAYLOAD
        )
    assert [(str(e.value), e.value.code) for e in (built, updated, extracted)] == [
        ("build_frame failed: Unknown error", None),
        ("update_frame failed: Unknown error", None),
        ("extract_signals failed: Unknown error", None),
    ]


# A C entry, by the symbol the library exports.
EntrySymbol = NewType("EntrySymbol", str)

# What a string entry answers, as its bytes.
Answer = NewType("Answer", bytes)


class _StringEntry(NamedTuple):
    """A string entry, by the symbol the library exports, and a call of it on a backend."""

    symbol: EntrySymbol
    call: Callable[[FFIBackend], Answer]


# Each call below hands the entry state 0, which the null stand-in ignores.


def _process(backend: FFIBackend) -> Answer:
    return Answer(backend.process(0, b"{}"))


def _send_frame(backend: FFIBackend) -> Answer:
    return Answer(
        backend.send_frame_binary(
            0,
            timestamp=_TIMESTAMP,
            can_id=_CAN_ID,
            extended=False,
            dlc=_DLC,
            data=_PAYLOAD,
            brs=None,
            esi=None,
        )
    )


def _send_error(backend: FFIBackend) -> Answer:
    return Answer(backend.send_error_binary(0, _TIMESTAMP))


def _send_remote(backend: FFIBackend) -> Answer:
    return Answer(
        backend.send_remote_binary(0, timestamp=_TIMESTAMP, can_id=_CAN_ID, extended=False)
    )


def _start_stream(backend: FFIBackend) -> Answer:
    return Answer(backend.start_stream_binary(0))


def _end_stream(backend: FFIBackend) -> Answer:
    return Answer(backend.end_stream_binary(0))


def _format_dbc(backend: FFIBackend) -> Answer:
    return Answer(backend.format_dbc_binary(0))


def _extract_signals(backend: FFIBackend) -> Answer:
    return Answer(
        backend.extract_signals_binary(0, can_id=_CAN_ID, extended=False, dlc=_DLC, data=_PAYLOAD)
    )


_STRING_ENTRIES = [
    _StringEntry(EntrySymbol("aletheia_process"), _process),
    _StringEntry(EntrySymbol("aletheia_send_frame"), _send_frame),
    _StringEntry(EntrySymbol("aletheia_send_error"), _send_error),
    _StringEntry(EntrySymbol("aletheia_send_remote"), _send_remote),
    _StringEntry(EntrySymbol("aletheia_start_stream"), _start_stream),
    _StringEntry(EntrySymbol("aletheia_end_stream"), _end_stream),
    _StringEntry(EntrySymbol("aletheia_format_dbc"), _format_dbc),
    _StringEntry(EntrySymbol("aletheia_extract_signals"), _extract_signals),
]


@pytest.mark.parametrize("entry", _STRING_ENTRIES, ids=[e.symbol for e in _STRING_ENTRIES])
def test_a_string_entry_answering_null_is_an_ffi_error_naming_it(entry: _StringEntry) -> None:
    """A string entry the library answers with a null string is an ``FFIError`` naming it."""
    backend = FFIBackend(lib_path=stand_in_kernel(_NULL))
    with pytest.raises(AletheiaError) as refused:
        _ = entry.call(backend)
    assert (type(refused.value), str(refused.value), refused.value.code) == (
        FFIError,
        f"{entry.symbol} returned null",
        None,
    )


def test_a_string_entry_releases_the_string_it_answered() -> None:
    """A string entry's answer is read, then its string is released through the library.

    The recording stand-in counts each string released to it, a NULL releasing nothing.
    """
    backend = _recording()
    state = backend.init()
    released = _kept().aletheia_test_free_count
    before = Count(released())
    answered = backend.start_stream_binary(state)
    assert (answered, Count(released())) == (_refused(Quote("start_stream")), Count(before + 1))
