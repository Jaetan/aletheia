#!/usr/bin/env bash
# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
#
# Probes src/Aletheia/CAN/BatchFrameBuilding.agda.
# Claim: a frame is built only at a DLC whose bytes hold every signal the
# request places. The caller's DLC sizes the frame and the DBC places the
# bits, and the bit writer is total: a signal reaching past the end would have
# its overhanging bits written nowhere and the frame answered as if it carried
# them. The builder names the first such signal instead, on the same geometry
# proposition the ingest gates decide. Shown through the library itself, on a
# message whose two signals occupy the first four bytes: every DLC from four
# up builds a frame of that many bytes, and every DLC below it is refused,
# naming the first signal that does not fit, with nothing written. Non-zero
# exit: a frame is built at a DLC that cannot hold its signals, a DLC that can
# is refused, or a refusal writes. Exits 0 with a note when the library is not
# built.
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

lib = ctypes.CDLL(sys.argv[1])
argc = ctypes.c_int(1)
argv = (ctypes.c_char_p * 2)(ctypes.c_char_p(b"probe"), None)
lib.hs_init(ctypes.byref(argc), ctypes.byref(ctypes.cast(argv, ctypes.POINTER(ctypes.c_char_p))))
lib.aletheia_init.restype = ctypes.c_void_p
state = lib.aletheia_init()
lib.aletheia_process.restype = ctypes.c_char_p
lib.aletheia_process.argtypes = [ctypes.c_void_p, ctypes.c_char_p]


def signal(name, start):
    return {
        "name": name, "startBit": start, "length": 16, "byteOrder": "little_endian",
        "signed": False, "factor": 1, "offset": 0, "minimum": 0, "maximum": 65535,
        "unit": "", "presence": "always", "receivers": [],
    }


dbc = {
    "version": "1.0",
    "messages": [{
        "id": 256, "name": "M", "dlc": 8, "sender": "ECU", "extended": False,
        "signals": [signal("Speed", 0), signal("Rpm", 16)],
    }],
    "environmentVars": [],
}
loaded = lib.aletheia_process(state, json.dumps({"type": "command", "command": "parseDBC", "dbc": dbc}).encode())
if b'"status": "success"' not in loaded:
    print(f"the DBC did not load: {loaded[:120]!r}")
    sys.exit(1)

build = lib.aletheia_build_frame_bin
build.restype = ctypes.c_int8
build.argtypes = [
    ctypes.c_void_p, ctypes.c_uint32, ctypes.c_uint8, ctypes.c_uint8, ctypes.c_uint32,
    ctypes.POINTER(ctypes.c_uint32), ctypes.POINTER(ctypes.c_int64), ctypes.POINTER(ctypes.c_int64),
    ctypes.POINTER(ctypes.c_uint8), ctypes.POINTER(ctypes.c_char_p),
]
indices = (ctypes.c_uint32 * 2)(0, 1)
numerators = (ctypes.c_int64 * 2)(1000, 3000)
denominators = (ctypes.c_int64 * 2)(1, 1)

# The two signals occupy bits 0 to 31, so four bytes hold them and three do
# not. The buffer is longer than any frame and every byte is set, so a write
# of any length shows.
SET = 0xFF
BUFFER = 64
HOLDS_THEM = 4
failures = []
for dlc in range(0, 9):
    out = (ctypes.c_uint8 * BUFFER)(*([SET] * BUFFER))
    err = ctypes.c_char_p()
    status = build(state, 256, 0, dlc, 2, indices, numerators, denominators, out, ctypes.byref(err))
    message = err.value.decode() if err.value else ""
    # The length of what was written: the first index from which every byte
    # is still set. An untouched buffer answers zero.
    raw = bytes(out)
    written = next(i for i in range(BUFFER + 1) if raw[i:] == bytes([SET]) * (BUFFER - i))
    if dlc >= HOLDS_THEM:
        if status != 0:
            failures.append(f"DLC {dlc} holds both signals and was refused as {message!r}")
        elif written != dlc:
            failures.append(f"DLC {dlc} built a frame of {written} bytes, not {dlc}")
    elif status != 1:
        failures.append(f"DLC {dlc} cannot hold the signals and was accepted with status {status}")
    elif "does not fit a frame of size" not in message:
        failures.append(f"DLC {dlc} was refused as {message!r}, which does not name the geometry")
    elif written != 0:
        failures.append(f"DLC {dlc} was refused and still wrote {written} bytes")

for line in failures:
    print(line)
sys.exit(1 if failures else 0)
PY
