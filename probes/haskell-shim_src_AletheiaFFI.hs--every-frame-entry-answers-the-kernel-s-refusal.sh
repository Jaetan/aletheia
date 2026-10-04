#!/usr/bin/env bash
# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
#
# Probes haskell-shim/src/AletheiaFFI.hs.
# Claim: every C entry that takes a frame hands the caller's fields to the
# kernel's frame parser unchecked and answers its refusal, before any state
# changes. A standard identifier past 11 bits, an extended one past 29 bits
# and a DLC code past 15 are refused with their parse_* code by each of
# aletheia_send_frame, aletheia_extract_signals, aletheia_build_frame_bin,
# aletheia_update_frame_bin and aletheia_extract_signals_bin, the identifiers
# by aletheia_send_remote too; a payload one byte short of its DLC's count,
# one byte over it, or past the 64 bytes of the largest code is refused with
# parse_payload_length_mismatch by each entry that reads a payload. A build or
# an update writes nothing into the caller's buffer while refusing, and a
# frame refused mid-stream leaves the stream's clock where it was. Shown by
# calling each entry through the library itself, every buffer byte set, and
# by sending an accepted frame with an earlier timestamp after each refusal.
# Non-zero exit: an entry accepts such a frame, refuses it with another code,
# writes while refusing, or moves the clock. Exits 0 with a note when the
# library is not built.
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


def take(pointer):
    text = ctypes.string_at(pointer).decode()
    lib.aletheia_free_str(pointer)
    return json.loads(text)


def signal(name, start):
    return {
        "name": name, "startBit": start, "length": 16, "byteOrder": "little_endian",
        "signed": False, "factor": 1, "offset": 0, "minimum": 0, "maximum": 65535,
        "unit": "", "presence": "always", "receivers": [],
    }


def process(command):
    body = json.dumps(command).encode()
    return take(lib.aletheia_process(state, ctypes.byref(AletheiaText(body, len(body)))))


dbc = {
    "version": "1.0",
    "messages": [{
        "id": 256, "name": "M", "dlc": 8, "sender": "ECU", "extended": False,
        "signals": [signal("Speed", 0), signal("Rpm", 16)],
    }],
    "environmentVars": [],
}
loaded = process({"type": "command", "command": "parseDBC", "dbc": dbc})
if loaded.get("status") != "success":
    print(f"the DBC did not load: {loaded}")
    sys.exit(1)

kept = []


def frame(timestamp, can_id, extended, dlc, length):
    data = (ctypes.c_uint8 * max(length, 1))(*([0] * max(length, 1)))
    kept.append(data)
    return AletheiaFrame(timestamp=timestamp, data=ctypes.cast(data, ctypes.POINTER(ctypes.c_uint8)),
                         can_id=can_id, extended=extended, dlc=dlc, data_len=length)


values = AletheiaSignalValues(
    indices=(ctypes.c_uint32 * 2)(0, 1),
    numerators=(ctypes.c_int64 * 2)(1000, 3000),
    denominators=(ctypes.c_int64 * 2)(1, 1),
    count=2,
)
SET = 0xFF
BUFFER = 512


def binary(entry, f):
    out = (ctypes.c_uint8 * BUFFER)(*([SET] * BUFFER))
    buffer = AletheiaBuffer(data=out, size=BUFFER)
    if entry is lib.aletheia_extract_signals_bin:
        status = entry(state, ctypes.byref(f), ctypes.byref(buffer))
    else:
        status = entry(state, ctypes.byref(f), ctypes.byref(values), ctypes.byref(buffer))
    answer = {}
    if status == 1 and buffer.err:
        text = ctypes.string_at(buffer.err).decode()
        try:
            answer = json.loads(text)
        except json.JSONDecodeError:
            answer = {"not an envelope": text}
    written = entry is not lib.aletheia_extract_signals_bin and any(byte != SET for byte in out)
    return status, answer, written


def json_entry(entry, f):
    return take(entry(state, ctypes.byref(f)))


ID_RULES = [
    ("standard identifier 2048", (2048, 0, 8, 8), "parse_std_can_id_out_of_range"),
    ("extended identifier 2^29", (1 << 29, 1, 8, 8), "parse_ext_can_id_out_of_range"),
    ("DLC 16", (256, 0, 16, 8), "parse_dlc_code_out_of_range"),
]
PAYLOAD_RULES = [
    ("7 bytes against DLC 8", (256, 0, 8, 7), "parse_payload_length_mismatch"),
    ("9 bytes against DLC 8", (256, 0, 8, 9), "parse_payload_length_mismatch"),
    ("65 bytes against DLC 15", (256, 0, 15, 65), "parse_payload_length_mismatch"),
]
READS_PAYLOAD = {"send_frame", "extract_signals", "update_frame_bin", "extract_signals_bin"}
failures = []

for entry_name in ("extract_signals", "build_frame_bin", "update_frame_bin", "extract_signals_bin"):
    entry = getattr(lib, f"aletheia_{entry_name}")
    rules = ID_RULES + (PAYLOAD_RULES if entry_name in READS_PAYLOAD else [])
    for label, fields, code in rules:
        f = frame(0, *fields)
        if entry_name.endswith("_bin"):
            status, answer, written = binary(entry, f)
            if status != 1 or answer.get("code") != code:
                failures.append(f"{entry_name}, {label}: status {status}, {answer}, wanted {code}")
            elif written:
                failures.append(f"{entry_name}, {label}: refused and wrote into the buffer")
        else:
            answer = json_entry(entry, f)
            if answer.get("code") != code:
                failures.append(f"{entry_name}, {label}: answered {answer}, wanted {code}")

started = take(lib.aletheia_start_stream(state))
if started.get("status") != "success":
    print(f"the stream did not start: {started}")
    sys.exit(1)
clock = 1000
for entry_name, rules in (("send_frame", ID_RULES + PAYLOAD_RULES), ("send_remote", ID_RULES[:2])):
    entry = getattr(lib, f"aletheia_{entry_name}")
    for label, fields, code in rules:
        answer = json_entry(entry, frame(clock + 5000, *fields))
        if answer.get("code") != code:
            failures.append(f"{entry_name}, {label}: answered {answer}, wanted {code}")
        after = json_entry(lib.aletheia_send_frame, frame(clock, 256, 0, 8, 8))
        if after.get("status") != "ack":
            failures.append(f"{entry_name}, {label}: an earlier frame after the refusal got {after}")
        clock += 1

lib.aletheia_close(state)
for line in failures:
    print(line)
sys.exit(1 if failures else 0)
PY
