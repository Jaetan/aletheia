#!/usr/bin/env bash
# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
#
# Probes src/Aletheia/CAN/BatchFrameBuilding.agda.
# Claim: a build and an update both refuse a request naming two signals that
# share a bit, with frame_signals_overlap and nothing written: of two writes
# to one bit only the later would remain. Two multiplexed signals over the
# same bits are such a pair, and so is one signal named twice; each signal
# alone is written. Shown through the library itself, on a message whose
# PayloadA (Mode 0) and PayloadB (Mode 1) both occupy bits 8 to 23. Non-zero
# exit: an entry accepts an overlapping request, refuses it with another code,
# writes while refusing, or refuses a single signal. Exits 0 with a note when
# the library is not built.
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

text = (
    'VERSION ""\n\nNS_ :\n\nBS_:\n\nBU_: ECU\n\nBO_ 100 BasicMux: 8 ECU\n'
    ' SG_ Mode M : 0|4@1+ (1,0) [0|15] "" ECU\n'
    ' SG_ PayloadA m0 : 8|16@1+ (1,0) [0|65535] "" ECU\n'
    ' SG_ PayloadB m1 : 8|16@1+ (1,0) [0|65535] "" ECU\n\n'
)
body = json.dumps({"type": "command", "command": "parseDBCText", "text": text}).encode()
pointer = lib.aletheia_process(state, ctypes.byref(AletheiaText(body, len(body))))
loaded = json.loads(ctypes.string_at(pointer).decode())
lib.aletheia_free_str(pointer)
if loaded.get("status") != "success":
    print(f"the DBC did not load: {loaded}")
    sys.exit(1)
names = [s["name"] for s in loaded["dbc"]["messages"][0]["signals"]]
A, B = names.index("PayloadA"), names.index("PayloadB")

SET = 0xAB
BUFFER = 64
kept = []


def call(entry, indices):
    out = (ctypes.c_uint8 * BUFFER)(*([SET] * BUFFER))
    buffer = AletheiaBuffer(data=out, size=BUFFER)
    data = (ctypes.c_uint8 * 8)(*([0] * 8))
    kept.append(data)
    frame = AletheiaFrame(timestamp=0, data=ctypes.cast(data, ctypes.POINTER(ctypes.c_uint8)),
                          can_id=100, extended=0, dlc=8, data_len=8)
    count = len(indices)
    values = AletheiaSignalValues(
        indices=(ctypes.c_uint32 * count)(*indices),
        numerators=(ctypes.c_int64 * count)(*([1] * count)),
        denominators=(ctypes.c_int64 * count)(*([1] * count)),
        count=count,
    )
    status = entry(state, ctypes.byref(frame), ctypes.byref(values), ctypes.byref(buffer))
    answer = json.loads(ctypes.string_at(buffer.err).decode()) if status == 1 and buffer.err else {}
    return status, answer, bytes(out)


failures = []
for entry_name in ("build_frame_bin", "update_frame_bin"):
    entry = getattr(lib, f"aletheia_{entry_name}")
    for label, indices in (("PayloadA and PayloadB", [A, B]), ("PayloadA twice", [A, A])):
        status, answer, out = call(entry, indices)
        if status != 1 or answer.get("code") != "frame_signals_overlap":
            failures.append(f"{entry_name}, {label}: status {status}, {answer}, wanted frame_signals_overlap")
        elif out != bytes([SET]) * BUFFER:
            failures.append(f"{entry_name}, {label}: refused and wrote into the buffer")
    for label, indices in (("PayloadA alone", [A]), ("PayloadB alone", [B])):
        status, answer, _ = call(entry, indices)
        if status != 0:
            failures.append(f"{entry_name}, {label}: refused as {answer}")

lib.aletheia_close(state)
for line in failures:
    print(line)
sys.exit(1 if failures else 0)
PY
