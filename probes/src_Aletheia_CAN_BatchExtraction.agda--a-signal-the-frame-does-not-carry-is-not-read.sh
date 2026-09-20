#!/usr/bin/env bash
# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
#
# Probes src/Aletheia/CAN/SignalExtraction.agda.
# Claim: a signal whose last bit lies past the end of the frame that arrived
# is reported, not read. The bit reader is total and answers zero for bits
# that are not there, which would be a value the frame does not carry; the
# extractor asks the geometry the ingest gates decide, of the frame's own
# size, and routes the signal to the error stream instead. Shown through the
# library on a message whose two signals occupy the first four bytes: at four
# bytes and above both read, at two only the first reads and the second is an
# error, at one both are errors and no value is reported. Non-zero exit: a
# signal the frame does not carry is given a value, or one it carries is
# refused. Exits 0 with a note when the library is not built.
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

extract = lib.aletheia_extract_signals
extract.restype = ctypes.c_char_p
extract.argtypes = [
    ctypes.c_void_p, ctypes.c_uint32, ctypes.c_uint8, ctypes.c_uint8,
    ctypes.POINTER(ctypes.c_uint8), ctypes.c_uint8,
]

# Speed occupies bits 0 to 15 and Rpm bits 16 to 31, so four bytes carry both,
# two carry only Speed, and one carries neither.
CARRIES = {0: (), 1: (), 2: ("Speed",), 4: ("Speed", "Rpm"), 8: ("Speed", "Rpm")}
PAYLOAD = [0xE8, 0x03, 0xB8, 0x0B, 0, 0, 0, 0]
failures = []
for dlc, carried in sorted(CARRIES.items()):
    data = (ctypes.c_uint8 * dlc)(*PAYLOAD[:dlc]) if dlc else None
    answer = json.loads(extract(state, 256, 0, dlc, data, dlc).decode())
    read = {v["name"] for v in answer.get("values", [])}
    refused = {e["name"]: e["error"] for e in answer.get("errors", [])}
    if read != set(carried):
        failures.append(f"a frame of {dlc} bytes carries {sorted(carried)}, and {sorted(read)} were read")
    for name in ("Speed", "Rpm"):
        if name in carried:
            continue
        if name not in refused:
            failures.append(f"a frame of {dlc} bytes does not carry {name}, and nothing was reported")
        elif "does not fit the frame" not in refused[name]:
            failures.append(f"{name} at {dlc} bytes was reported as {refused[name]!r}, which does not name the geometry")

for line in failures:
    print(line)
sys.exit(1 if failures else 0)
PY
