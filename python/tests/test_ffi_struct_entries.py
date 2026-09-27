# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
"""The kernel's structure-taking entries, called raw through ``ctypes``.

The bindings never pass a NULL structure or a buffer smaller than the frame,
so the refusals the shim holds for them are reachable only from here: a NULL
frame, NULL signal values or a NULL result buffer is refused cleanly, a result
buffer that cannot hold the frame is refused before a byte is written, and a
build reports the count it wrote.
"""

from __future__ import annotations

import ctypes
from typing import TYPE_CHECKING

import pytest
from _dbc_helpers import dbc, message, signal

from aletheia.client._ffi import (
    AletheiaBuffer,
    AletheiaFrame,
    AletheiaSignalValues,
    configure_ffi_signatures,
    find_ffi_library,
)
from aletheia.types import ParseDBCCommand, dump_json

if TYPE_CHECKING:
    from collections.abc import Iterator

pytestmark = pytest.mark.usefixtures("rts_up")

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


@pytest.fixture(name="state")
def _state() -> Iterator[int]:
    """Open a session with the two-signal DBC loaded, and close it after."""
    state: int = _LIB.aletheia_init()
    _take_string(_LIB.aletheia_process(state, dump_json(_PARSE_DBC).encode()))
    try:
        yield state
    finally:
        _LIB.aletheia_close(state)


def _take_string(pointer: int) -> str:
    """Read a string the kernel allocated, and free it."""
    try:
        return ctypes.string_at(pointer).decode()
    finally:
        _LIB.aletheia_free_str(pointer)


def _error(buffer: AletheiaBuffer) -> str:
    """Read and free the error a failed entry set on ``buffer``."""
    err: int | None = buffer.err
    assert err is not None
    return _take_string(err)


def _values() -> AletheiaSignalValues:
    return AletheiaSignalValues(
        indices=(ctypes.c_uint32 * 2)(0, 1),
        numerators=(ctypes.c_int64 * 2)(1000, 3000),
        denominators=(ctypes.c_int64 * 2)(1, 1),
        count=2,
    )


def _frame(dlc: int = 8) -> AletheiaFrame:
    payload = (ctypes.c_uint8 * dlc)()
    return AletheiaFrame(data=payload, can_id=256, dlc=dlc, data_len=dlc)


def _filled() -> ctypes.Array[ctypes.c_uint8]:
    return (ctypes.c_uint8 * _CAPACITY)(*([_SET] * _CAPACITY))


def test_a_null_frame_is_refused_by_every_entry_that_takes_one(state: int) -> None:
    """Every frame-taking entry answers a NULL frame with an error, not a crash."""
    for entry in (_LIB.aletheia_send_frame, _LIB.aletheia_extract_signals):
        assert "null frame" in _take_string(entry(state, None))
    values = _values()
    for entry in (_LIB.aletheia_build_frame_bin, _LIB.aletheia_update_frame_bin):
        out = AletheiaBuffer(data=_filled(), size=_CAPACITY)
        assert entry(state, None, ctypes.byref(values), ctypes.byref(out)) == 1
        assert "null frame" in _error(out)
    out = AletheiaBuffer()
    assert _LIB.aletheia_extract_signals_bin(state, None, ctypes.byref(out)) == 1
    assert "null frame" in _error(out)


def test_null_signal_values_are_refused(state: int) -> None:
    """Build and update answer NULL signal values with an error."""
    frame = _frame()
    for entry in (_LIB.aletheia_build_frame_bin, _LIB.aletheia_update_frame_bin):
        out = AletheiaBuffer(data=_filled(), size=_CAPACITY)
        assert entry(state, ctypes.byref(frame), None, ctypes.byref(out)) == 1
        assert "null signal values" in _error(out)


def test_a_null_result_buffer_is_refused(state: int) -> None:
    """With nowhere to write even an error, the entries answer failure alone."""
    frame = _frame()
    values = _values()
    for entry in (_LIB.aletheia_build_frame_bin, _LIB.aletheia_update_frame_bin):
        assert entry(state, ctypes.byref(frame), ctypes.byref(values), None) == 1
    assert _LIB.aletheia_extract_signals_bin(state, ctypes.byref(frame), None) == 1


def test_a_buffer_smaller_than_the_frame_is_refused_before_a_write(state: int) -> None:
    """Build and update refuse a buffer that cannot hold the DLC's bytes, writing none."""
    frame = _frame()
    values = _values()
    for entry in (_LIB.aletheia_build_frame_bin, _LIB.aletheia_update_frame_bin):
        target = _filled()
        out = AletheiaBuffer(data=target, size=7)
        assert entry(state, ctypes.byref(frame), ctypes.byref(values), ctypes.byref(out)) == 1
        assert "out size 7 < dlcToBytes 8" in _error(out)
        assert bytes(target) == bytes([_SET]) * _CAPACITY
        assert out.size == 7
        unset = AletheiaBuffer(size=_CAPACITY)
        assert entry(state, ctypes.byref(frame), ctypes.byref(values), ctypes.byref(unset)) == 1
        assert "null out buffer" in _error(unset)


def test_a_build_reports_the_count_it_wrote(state: int) -> None:
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
