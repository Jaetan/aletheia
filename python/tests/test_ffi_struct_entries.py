# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
"""The kernel's structure-taking entries, called raw through ``ctypes``.

The bindings never pass a NULL structure or a buffer smaller than the frame,
so the refusals the shim holds for them are reachable only from here: a NULL
frame, NULL signal values or a NULL result buffer is refused cleanly, a result
buffer that cannot hold the frame is refused before a byte is written, a build
reports the count it wrote, a text the header refuses or a NULL result is
refused by every entry reading a text, and every entry reading a text writes
every field of its result on every call, the stand-ins as the kernel. The
envelope a refused entry leaves is freed once the binding has read it. Every
argument of every entry is held to the header's type, one of another type
refused before the library runs, and the property check answers its status as
a number.
"""

from __future__ import annotations

import ctypes
import json
from fractions import Fraction
from typing import TYPE_CHECKING, NewType

import pytest
from _dbc_helpers import dbc, message, signal
from _stand_in import StandInName, stand_in_kernel

from aletheia import Signal
from aletheia.client._ffi import (
    AletheiaBuffer,
    AletheiaDecimal,
    AletheiaFrame,
    AletheiaPropertyCheck,
    AletheiaRational,
    AletheiaSignalValues,
    AletheiaText,
    AletheiaTimeBound,
    KernelResponse,
    Magnitude,
    configure_ffi_signatures,
    find_ffi_library,
    parse_json_object,
    take_error_envelope,
    uint128_value,
    wire_rational,
)
from aletheia.common_types import Prose
from aletheia.types import ParseDBCCommand, dump_json

if TYPE_CHECKING:
    from collections.abc import Iterator

pytestmark = pytest.mark.usefixtures("rts_up")

# The opaque session handle ``aletheia_init`` answers.
StateHandle = NewType("StateHandle", int)

_LIB = ctypes.CDLL(str(find_ffi_library()))
configure_ffi_signatures(_LIB)

# Speed occupies bits 0 to 15 and Rpm bits 16 to 31 of message 256.
_PARSE_DBC: ParseDBCCommand = {
    "type": "command",
    "command": "parseDBC",
    "dbc": dbc([message(256, "M", [signal("Speed"), signal("Rpm", start_bit=16)])]),
}

_SET = 0xFF
_CAPACITY = 64
# The address an error left unwritten reads as, every byte of its result set.
_UNWRITTEN = 2**64 - 1


@pytest.fixture(name="state")
def _state() -> Iterator[StateHandle]:
    """Open a session with the two-signal DBC loaded, and close it after."""
    state = StateHandle(_LIB.aletheia_init())
    command = dump_json(_PARSE_DBC).encode()
    _take_response(_LIB.aletheia_process(state, ctypes.byref(AletheiaText(command, len(command)))))
    try:
        yield state
    finally:
        _LIB.aletheia_close(state)


def _take_response(pointer: int) -> KernelResponse:
    """Read the bytes of a string the kernel allocated, and free it."""
    try:
        return KernelResponse(ctypes.string_at(pointer))
    finally:
        _LIB.aletheia_free_str(pointer)


def _error(buffer: AletheiaBuffer) -> str:
    """Read and free the shim's refusal set on ``buffer``, and answer its message.

    The refusal is the JSON envelope every entry answers with, carrying the
    shim's own code.
    """
    err: int | None = buffer.err
    assert err is not None
    envelope = parse_json_object(_take_response(err))
    assert envelope["status"] == "error"
    assert envelope["code"] == "ffi_validation_error"
    reason = envelope["message"]
    assert isinstance(reason, str)
    return reason


def _values() -> AletheiaSignalValues:
    return AletheiaSignalValues(
        indices=(ctypes.c_uint32 * 2)(0, 1),
        values=(AletheiaRational * 2)(wire_rational(Fraction(1000)), wire_rational(Fraction(3000))),
        count=2,
    )


def _frame(dlc: int = 8) -> AletheiaFrame:
    payload = (ctypes.c_uint8 * dlc)()
    return AletheiaFrame(data=payload, can_id=256, dlc=dlc, data_len=dlc)


def _filled() -> ctypes.Array[ctypes.c_uint8]:
    return (ctypes.c_uint8 * _CAPACITY)(*([_SET] * _CAPACITY))


def test_a_null_frame_is_refused_by_every_entry_that_takes_one(state: StateHandle) -> None:
    """Every frame-taking entry answers a NULL frame with an error, not a crash."""
    for entry in (_LIB.aletheia_send_frame, _LIB.aletheia_extract_signals):
        envelope = parse_json_object(_take_response(entry(state, None)))
        assert "null frame" in str(envelope["message"])
    values = _values()
    for entry in (_LIB.aletheia_build_frame_bin, _LIB.aletheia_update_frame_bin):
        out = AletheiaBuffer(data=_filled(), size=_CAPACITY)
        assert entry(state, None, ctypes.byref(values), ctypes.byref(out)) == 1
        assert "null frame" in _error(out)
    out = AletheiaBuffer()
    assert _LIB.aletheia_extract_signals_bin(state, None, ctypes.byref(out)) == 1
    assert "null frame" in _error(out)


def test_null_signal_values_are_refused(state: StateHandle) -> None:
    """Build and update answer NULL signal values with an error."""
    frame = _frame()
    for entry in (_LIB.aletheia_build_frame_bin, _LIB.aletheia_update_frame_bin):
        out = AletheiaBuffer(data=_filled(), size=_CAPACITY)
        assert entry(state, ctypes.byref(frame), None, ctypes.byref(out)) == 1
        assert "null signal values" in _error(out)


def test_a_null_result_buffer_is_refused(state: StateHandle) -> None:
    """With nowhere to write even an error, the entries answer failure alone."""
    frame = _frame()
    values = _values()
    for entry in (_LIB.aletheia_build_frame_bin, _LIB.aletheia_update_frame_bin):
        assert entry(state, ctypes.byref(frame), ctypes.byref(values), None) == 1
    assert _LIB.aletheia_extract_signals_bin(state, ctypes.byref(frame), None) == 1


def test_a_buffer_smaller_than_the_frame_is_refused_before_a_write(state: StateHandle) -> None:
    """Build and update refuse a buffer that cannot hold the DLC's bytes, writing none."""
    frame = _frame()
    values = _values()
    for entry in (_LIB.aletheia_build_frame_bin, _LIB.aletheia_update_frame_bin):
        target = _filled()
        out = AletheiaBuffer(data=target, size=7)
        assert entry(state, ctypes.byref(frame), ctypes.byref(values), ctypes.byref(out)) == 1
        assert "out size 7 < 8 frame bytes" in _error(out)
        assert bytes(target) == bytes([_SET]) * _CAPACITY
        assert out.size == 7
        unset = AletheiaBuffer(size=_CAPACITY)
        assert entry(state, ctypes.byref(frame), ctypes.byref(values), ctypes.byref(unset)) == 1
        assert "null out buffer" in _error(unset)


def test_a_build_reports_the_count_it_wrote(state: StateHandle) -> None:
    """A buffer larger than the frame comes back holding the frame, its size the frame's."""
    frame = _frame()
    values = _values()
    for entry in (_LIB.aletheia_build_frame_bin, _LIB.aletheia_update_frame_bin):
        target = _filled()
        out = AletheiaBuffer(data=target, size=_CAPACITY)
        assert entry(state, ctypes.byref(frame), ctypes.byref(values), ctypes.byref(out)) == 0
        assert out.size == 8
        assert bytes(target)[:4] == bytes([0xE8, 0x03, 0xB8, 0x0B])
        assert bytes(target)[8:] == bytes([_SET]) * (_CAPACITY - 8)


def test_a_text_the_header_refuses_is_refused_by_every_text_entry(state: StateHandle) -> None:
    """A text the header refuses is refused by every entry reading one before a byte is read.

    That is a NULL text, NULL data under a non-zero size, and a size past what
    the library can index; NULL data of size 0 is the empty text, which
    reaches the parser.
    """
    for text, reason in (
        (None, "null input"),
        (AletheiaText(None, 3), "null input"),
        (AletheiaText(None, 2**63), "input size is out of range"),
    ):
        argument = None if text is None else ctypes.byref(text)
        response = json.loads(_take_response(_LIB.aletheia_process(state, argument)))
        assert response == {"status": "error", "code": "ffi_validation_error", "message": reason}
        decimal = _prefilled(AletheiaDecimal())
        time_bound = _prefilled(AletheiaTimeBound())
        check = _prefilled(AletheiaPropertyCheck())
        for entry, out in (
            (_LIB.aletheia_parse_decimal, decimal),
            (_LIB.aletheia_parse_time_bound, time_bound),
            (_LIB.aletheia_check_property, check),
        ):
            assert entry(argument, ctypes.byref(out)) == 1
            assert out.err != _UNWRITTEN
            envelope = json.loads(_take_response(out.err))
            expected = {"status": "error", "code": "ffi_validation_error", "message": reason}
            assert envelope == expected
        assert (_fields(decimal.value), time_bound.microseconds) == (_ZERO, 0)
    empty_text = ctypes.byref(AletheiaText(None, 0))
    empty = json.loads(_take_response(_LIB.aletheia_process(state, empty_text)))
    assert empty["code"] == "dispatch_invalid_json"


def test_a_null_result_is_refused_by_every_text_entry() -> None:
    """With nowhere to write even an error, an entry reading a text answers failure alone."""
    text = AletheiaText(b"1", 1)
    for entry in (
        _LIB.aletheia_parse_decimal,
        _LIB.aletheia_parse_time_bound,
        _LIB.aletheia_check_property,
    ):
        assert entry(ctypes.byref(text), None) == 1


# A text handed to an entry that reads one.
EntryText = NewType("EntryText", bytes)

_ZERO = (Magnitude(0), Magnitude(0), False)


def _prefilled[T: ctypes.Structure](out: T) -> T:
    """Set every byte of ``out``, so a field an entry leaves unwritten keeps them."""
    _ = ctypes.memset(ctypes.byref(out), _SET, ctypes.sizeof(out))
    return out


def _fields(value: AletheiaRational) -> tuple[Magnitude, Magnitude, bool]:
    """Every field of a rational as written: its numerator, its denominator, its sign byte set."""
    numerator, denominator = uint128_value(value.numerator), uint128_value(value.denominator)
    return (numerator, denominator, value.negative != 0)


def _text(raw: EntryText) -> AletheiaText:
    return AletheiaText(raw, len(raw))


_STAND_INS = [StandInName("null_kernel"), StandInName("recording_kernel")]


def test_a_decimal_that_holds_writes_its_error_as_null() -> None:
    """A parsed decimal writes NULL to its error, whatever the caller left there."""
    decimal = _prefilled(AletheiaDecimal())
    text = _text(EntryText(b"-1.5"))
    assert _LIB.aletheia_parse_decimal(ctypes.byref(text), ctypes.byref(decimal)) == 0
    assert (decimal.err, _fields(decimal.value)) == (None, (Magnitude(3), Magnitude(2), True))


def test_a_time_bound_that_holds_writes_its_error_as_null() -> None:
    """A parsed time bound writes NULL to its error, whatever the caller left there."""
    time_bound = _prefilled(AletheiaTimeBound())
    text = _text(EntryText(b"1500"))
    assert _LIB.aletheia_parse_time_bound(ctypes.byref(text), ctypes.byref(time_bound)) == 0
    assert (time_bound.err, time_bound.microseconds) == (None, 1500)


def test_a_property_that_holds_writes_its_error_as_null() -> None:
    """A property the kernel accepts writes NULL to its error, whatever the caller left there."""
    check = _prefilled(AletheiaPropertyCheck())
    text = _text(EntryText(dump_json(Signal("Speed").equals(1).always().to_dict()).encode()))
    assert _LIB.aletheia_check_property(ctypes.byref(text), ctypes.byref(check)) == 0
    assert check.err is None


def test_a_refused_decimal_writes_its_value_as_zero() -> None:
    """A decimal the kernel refuses writes zero to every field of its value beside the error."""
    decimal = _prefilled(AletheiaDecimal())
    text = _text(EntryText(b"x"))
    assert _LIB.aletheia_parse_decimal(ctypes.byref(text), ctypes.byref(decimal)) == 1
    assert decimal.err not in (None, _UNWRITTEN)
    _ = _take_response(decimal.err)
    assert _fields(decimal.value) == _ZERO


def test_a_refused_time_bound_writes_its_value_as_zero() -> None:
    """A time bound the kernel refuses writes zero to its microseconds beside the error."""
    time_bound = _prefilled(AletheiaTimeBound())
    text = _text(EntryText(b"-1"))
    assert _LIB.aletheia_parse_time_bound(ctypes.byref(text), ctypes.byref(time_bound)) == 1
    assert time_bound.err not in (None, _UNWRITTEN)
    _ = _take_response(time_bound.err)
    assert time_bound.microseconds == 0


def _stand_in(name: StandInName) -> ctypes.CDLL:
    lib = ctypes.CDLL(str(stand_in_kernel(name)))
    configure_ffi_signatures(lib)
    return lib


@pytest.mark.parametrize("name", _STAND_INS)
def test_a_stand_in_writes_every_field_of_a_decimal_it_refuses(name: StandInName) -> None:
    """A stand-in's refused decimal writes zero to its value, as the kernel's does."""
    lib = _stand_in(name)
    decimal = _prefilled(AletheiaDecimal())
    text = _text(EntryText(b"1"))
    assert lib.aletheia_parse_decimal(ctypes.byref(text), ctypes.byref(decimal)) == 1
    assert decimal.err != _UNWRITTEN
    lib.aletheia_free_str(decimal.err)
    assert _fields(decimal.value) == _ZERO


@pytest.mark.parametrize("name", _STAND_INS)
def test_a_stand_in_writes_every_field_of_a_time_bound_it_refuses(name: StandInName) -> None:
    """A stand-in's refused time bound writes zero to its microseconds, as the kernel's does."""
    lib = _stand_in(name)
    time_bound = _prefilled(AletheiaTimeBound())
    text = _text(EntryText(b"1"))
    assert lib.aletheia_parse_time_bound(ctypes.byref(text), ctypes.byref(time_bound)) == 1
    assert time_bound.err != _UNWRITTEN
    lib.aletheia_free_str(time_bound.err)
    assert time_bound.microseconds == 0


def test_the_envelope_a_refusal_left_is_freed_once_read() -> None:
    """The envelope of a refused entry is read whole, then freed through the library.

    The recording kernel counts the strings it frees, a NULL freeing nothing,
    so the count reads that the envelope's own block was released.
    """
    lib = _stand_in(StandInName("recording_kernel"))
    decimal = AletheiaDecimal()
    text = _text(EntryText(b"1"))
    assert lib.aletheia_parse_decimal(ctypes.byref(text), ctypes.byref(decimal)) == 1
    before = lib.aletheia_test_free_count()
    envelope = take_error_envelope(lib, decimal, Prose("no envelope"))
    assert envelope == {"status": "error", "code": "recording_kernel", "message": "parse_decimal"}
    assert lib.aletheia_test_free_count() == before + 1


# A kernel entry's symbol, as the header names it.
EntryName = NewType("EntryName", str)

# An argument's position in an entry's call, from zero.
ArgumentIndex = NewType("ArgumentIndex", int)

# What an entry's parameter points to, None for an address (``void *``).
type Pointee = type[ctypes.Structure | ctypes.c_uint8] | None

# The parameters of every entry that takes one, as the header declares them; a
# string the kernel answered is handed back by its address.
_POINTEES: dict[EntryName, tuple[Pointee, ...]] = {
    EntryName("aletheia_process"): (None, AletheiaText),
    EntryName("aletheia_free_str"): (None,),
    EntryName("aletheia_close"): (None,),
    EntryName("aletheia_send_frame"): (None, AletheiaFrame),
    EntryName("aletheia_start_stream"): (None,),
    EntryName("aletheia_end_stream"): (None,),
    EntryName("aletheia_format_dbc"): (None,),
    EntryName("aletheia_extract_signals"): (None, AletheiaFrame),
    EntryName("aletheia_send_error"): (None, AletheiaFrame),
    EntryName("aletheia_send_remote"): (None, AletheiaFrame),
    EntryName("aletheia_build_frame_bin"): (
        None,
        AletheiaFrame,
        AletheiaSignalValues,
        AletheiaBuffer,
    ),
    EntryName("aletheia_update_frame_bin"): (
        None,
        AletheiaFrame,
        AletheiaSignalValues,
        AletheiaBuffer,
    ),
    EntryName("aletheia_extract_signals_bin"): (None, AletheiaFrame, AletheiaBuffer),
    EntryName("aletheia_free_buf"): (ctypes.c_uint8,),
    EntryName("aletheia_format_rational"): (AletheiaRational,),
    EntryName("aletheia_parse_decimal"): (AletheiaText, AletheiaDecimal),
    EntryName("aletheia_parse_time_bound"): (AletheiaText, AletheiaTimeBound),
    EntryName("aletheia_check_property"): (AletheiaText, AletheiaPropertyCheck),
}

_ARGUMENTS = [
    (name, ArgumentIndex(at)) for name, pointees in _POINTEES.items() for at in range(len(pointees))
]

# The bytes of a buffer handed where a structure belongs, more than any of them holds.
_ROOM = 64


@pytest.mark.parametrize(
    ("name", "at"), _ARGUMENTS, ids=[f"{name}-{at + 1}" for name, at in _ARGUMENTS]
)
def test_an_argument_of_another_type_is_refused_before_the_library_runs(
    name: EntryName, at: ArgumentIndex
) -> None:
    """Each argument of each entry is held to the header's type at the call.

    An address refuses an integer object and a structure pointer a buffer of
    bytes, the other arguments as the binding hands them. The recording
    stand-in is the library, so an argument let through reaches an entry that
    reads only zeros.
    """
    lib = _stand_in(StandInName("recording_kernel"))
    pointees = _POINTEES[name]
    arguments = [
        (ctypes.c_ulong(0) if pointee is None else ctypes.create_string_buffer(_ROOM))
        if index == at
        else (None if pointee is None else ctypes.byref(pointee()))
        for index, pointee in enumerate(pointees)
    ]
    pointee = pointees[at]
    reason = (
        "'c_ulong' object cannot be interpreted as ctypes.c_void_p"
        if pointee is None
        else f"expected LP_{pointee.__name__} instance instead of c_char_Array_{_ROOM}"
    )
    with pytest.raises(ctypes.ArgumentError) as refused:
        getattr(lib, name)(*arguments)
    assert str(refused.value) == f"argument {at + 1}: TypeError: {reason}"


def test_a_stand_in_answers_the_property_it_refuses_with_status_one() -> None:
    """The property check's status is a number: 1 for a refusal, its envelope quoting the text."""
    lib = _stand_in(StandInName("recording_kernel"))
    check = AletheiaPropertyCheck()
    text = _text(EntryText(b"{}"))
    assert lib.aletheia_check_property(ctypes.byref(text), ctypes.byref(check)) == 1
    envelope = take_error_envelope(lib, check, Prose("no envelope"))
    assert envelope == {
        "status": "error",
        "code": "recording_kernel",
        "message": "check_property {}",
    }
