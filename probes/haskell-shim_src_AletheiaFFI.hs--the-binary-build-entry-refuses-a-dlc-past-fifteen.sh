#!/usr/bin/env bash
# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
#
# Probes haskell-shim/src/AletheiaFFI.hs.
# Claim: aletheia_build_frame_bin refuses a DLC code past 15 and writes
# nothing, the way the three other binary entries do through
# validateDLCAndLen. The code sizes the frame the kernel builds, and the DLC
# the caller passes is a raw byte, so a code past the last one would have the
# kernel fill a buffer the caller sized for eight. Shown by calling the entry
# through the library itself, with a buffer whose bytes are all set, at the
# code the wire allows and at one past it. Non-zero exit: the entry accepts a
# code past 15, or writes into the buffer while refusing, or refuses one the
# wire allows. Exits 0 with a note when the library is not built.
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

# The buffer holds more than the largest code a byte can carry, so a build
# that sizes the frame by the raw DLC writes inside it and is reported rather
# than corrupting this process; every byte is set, so a write of any length
# shows.
SET = 0xFF
BUFFER = 512
failures = []
for dlc, refused in ((8, False), (15, False), (16, True), (42, True), (255, True)):
    out = (ctypes.c_uint8 * BUFFER)(*([SET] * BUFFER))
    err = ctypes.c_char_p()
    status = build(state, 256, 0, dlc, 2, indices, numerators, denominators, out, ctypes.byref(err))
    message = err.value.decode() if err.value else ""
    untouched = all(byte == SET for byte in out)
    if refused:
        if status != 1:
            failures.append(f"DLC {dlc} was accepted with status {status}")
        elif "exceeds maximum (15)" not in message:
            failures.append(f"DLC {dlc} was refused as {message!r}, which does not name the bound")
        elif not untouched:
            written = next(i for i in range(BUFFER) if out[i] != SET)
            failures.append(f"DLC {dlc} was refused and still wrote from byte {written}")
    elif status != 0:
        failures.append(f"DLC {dlc} is on the wire and was refused as {message!r}")
    elif untouched:
        failures.append(f"DLC {dlc} reported success and wrote nothing")

for line in failures:
    print(line)
sys.exit(1 if failures else 0)
PY
