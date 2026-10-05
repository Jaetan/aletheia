#!/usr/bin/env bash
# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
#
# Probes src/Aletheia/CAN/Encoding/Value.agda.
# Claim: a build or an update writes a requested value only when it lies in
# the signal's declared [minimum, maximum] and an integer raw value scales to
# it exactly, and then the frame reads back the value requested, rounded
# nowhere. A value outside the range is refused with frame_value_out_of_range,
# naming the signal, the value and the range; a value off the factor's grid
# with frame_value_not_representable, naming the signal, the value, the
# factor and the offset; neither refusal writes. The cases run at a positive
# factor and at a negative one, which reverses which raw end gives which
# physical end, at both ends of each range and just past them. Shown through
# the library itself. Non-zero exit: a value is written that should be
# refused, refused that should be written, refused with another code or
# message, a refusal writes, or a written frame reads back another value.
# Exits 0 with a note when the library is not built.
set -u
cd "$(dirname "$0")/.." || exit 2
lib=build/libaletheia-ffi.so
py=python/.venv/bin/python
[ -f "$lib" ] || { echo "kernel not built, claim untestable"; exit 0; }
[ -x "$py" ] || exit 2
"$py" - "$lib" <<'PY'
import ctypes
import json
import sys
from fractions import Fraction

from aletheia.client._ffi import (
    AletheiaBuffer,
    AletheiaFrame,
    AletheiaSignalValues,
    AletheiaText,
    RTSState,
    configure_ffi_signatures,
)

lib = ctypes.CDLL(sys.argv[1])
configure_ffi_signatures(lib)
RTSState.acquire(lib)
state = lib.aletheia_init()


def take(pointer):
    text = ctypes.string_at(pointer).decode()
    lib.aletheia_free_str(pointer)
    return json.loads(text)


def signal(name, start, signed, factor, offset, minimum, maximum):
    return {
        "name": name, "startBit": start, "length": 8, "byteOrder": "little_endian",
        "signed": signed, "factor": factor, "offset": offset, "minimum": minimum,
        "maximum": maximum, "unit": "", "presence": "always", "receivers": [],
    }


# Half: unsigned at factor 1/2, so its bits carry 0 to 127.5 in steps of 1/2.
# Down: signed at factor -1/4 and offset 10, so raw -128 to 127 carry 42 down
# to -21.75 in steps of 1/4.  Each declared range is all its bits carry.
dbc = {
    "version": "1.0",
    "messages": [{
        "id": 256, "name": "M", "dlc": 8, "sender": "ECU", "extended": False,
        "signals": [
            signal("Half", 0, False, 0.5, 0, 0, 127.5),
            signal("Down", 8, True, -0.25, 10, -21.75, 42),
        ],
    }],
    "environmentVars": [],
}
body = json.dumps({"type": "command", "command": "parseDBC", "dbc": dbc}).encode()
loaded = take(lib.aletheia_process(state, ctypes.byref(AletheiaText(body, len(body)))))
if loaded.get("status") != "success":
    print(f"the DBC did not load: {loaded}")
    sys.exit(1)

F = Fraction
WRITTEN = [
    (0, "Half", F(3, 2)), (0, "Half", F(0)), (0, "Half", F(255, 2)),
    (1, "Down", F(42)), (1, "Down", F(-87, 4)), (1, "Down", F(41, 4)),
]
OUT_OF_RANGE = [
    (0, "Half", F(128), "value 128 for signal 'Half' is outside [0, 127.5]"),
    (0, "Half", F(-1, 2), "value -0.5 for signal 'Half' is outside [0, 127.5]"),
    (1, "Down", F(169, 4), "value 42.25 for signal 'Down' is outside [-21.75, 42]"),
    (1, "Down", F(-22), "value -22 for signal 'Down' is outside [-21.75, 42]"),
]
NOT_REPRESENTABLE = [
    (0, "Half", F(3, 10), "no integer raw value scales to value 0.3 for signal 'Half' (factor 0.5, offset 0)"),
    (0, "Half", F(5, 4), "no integer raw value scales to value 1.25 for signal 'Half' (factor 0.5, offset 0)"),
    (1, "Down", F(81, 8), "no integer raw value scales to value 10.125 for signal 'Down' (factor -0.25, offset 10)"),
]
SET = 0xAB
BUFFER = 64
kept = []


def frame_of(data):
    raw = (ctypes.c_uint8 * 8)(*data)
    kept.append(raw)
    return AletheiaFrame(timestamp=0, data=ctypes.cast(raw, ctypes.POINTER(ctypes.c_uint8)),
                         can_id=256, extended=0, dlc=8, data_len=8)


def call(entry, index, value):
    out = (ctypes.c_uint8 * BUFFER)(*([SET] * BUFFER))
    buffer = AletheiaBuffer(data=out, size=BUFFER)
    values = AletheiaSignalValues(
        indices=(ctypes.c_uint32 * 1)(index),
        numerators=(ctypes.c_int64 * 1)(value.numerator),
        denominators=(ctypes.c_int64 * 1)(value.denominator),
        count=1,
    )
    status = entry(state, ctypes.byref(frame_of([0] * 8)), ctypes.byref(values), ctypes.byref(buffer))
    answer = json.loads(ctypes.string_at(buffer.err).decode()) if status == 1 and buffer.err else {}
    return status, answer, bytes(out)


def read_back(data, name):
    answer = take(lib.aletheia_extract_signals(state, ctypes.byref(frame_of(data))))
    for entry in answer.get("values", []):
        if entry["name"] == name:
            value = entry["value"]
            return F(value["numerator"], value["denominator"]) if isinstance(value, dict) else F(value)
    return answer


failures = []
for entry_name in ("build_frame_bin", "update_frame_bin"):
    entry = getattr(lib, f"aletheia_{entry_name}")
    for index, name, value in WRITTEN:
        status, answer, out = call(entry, index, value)
        if status != 0:
            failures.append(f"{entry_name}, {name} = {value}: refused as {answer}")
            continue
        back = read_back(out[:8], name)
        if back != value:
            failures.append(f"{entry_name}, {name} = {value}: the frame reads back {back}")
    for code, cases in (("frame_value_out_of_range", OUT_OF_RANGE),
                        ("frame_value_not_representable", NOT_REPRESENTABLE)):
        for index, name, value, message in cases:
            status, answer, out = call(entry, index, value)
            if status != 1 or answer.get("code") != code or answer.get("message") != message:
                failures.append(f"{entry_name}, {name} = {value}: status {status}, {answer}, wanted {code}: {message}")
            elif out != bytes([SET]) * BUFFER:
                failures.append(f"{entry_name}, {name} = {value}: refused and wrote into the buffer")

lib.aletheia_close(state)
for line in failures:
    print(line)
sys.exit(1 if failures else 0)
PY
