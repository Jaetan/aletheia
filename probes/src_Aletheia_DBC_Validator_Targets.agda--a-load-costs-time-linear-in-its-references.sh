#!/usr/bin/env bash
# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
#
# Probes src/Aletheia/DBC/Validator/Targets.agda.
# Claim: loading a DBC costs time linear in its references to nodes and
# messages, up to a logarithm: each sender, additional sender, receiver and
# comment target is looked up in an index built once, not by scanning the
# list it names. A DBC of n messages where message i names node N{i} as its
# sender, N{i+1} as an additional sender, N{i} as its signal's receiver and
# is a comment's target, with n nodes declared, loads at 10,000 messages in at
# most 9 times its time at 2,500, the load scaling check's bound (x3 per
# doubling); a scan per reference grows 16-fold. Each time is the processor
# time a load takes, the least of three, the two sizes loaded in turn: what
# else the machine runs moves wall time and leaves this nearly alone, and what
# still moves it falls on both sizes alike. Shown through the library itself
# (parseDBC). Non-zero exit: a load is refused, or the growth passes 9. Exits
# 0 with a note when the library is not built.
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
import time

from aletheia.client._ffi import AletheiaText, RTSState, configure_ffi_signatures

lib = ctypes.CDLL(sys.argv[1])
configure_ffi_signatures(lib)
RTSState.acquire(lib)


def referenced(n):
    def message(i):
        return {"id": 0x100000 + i, "name": f"M{i}", "dlc": 8, "sender": f"N{i}", "extended": True,
                "senders": [f"N{(i + 1) % n}"],
                "signals": [{"name": f"S{i}", "startBit": 0, "length": 8, "byteOrder": "little_endian",
                             "signed": False, "factor": 1, "offset": 0, "minimum": 0, "maximum": 255,
                             "unit": "", "presence": "always", "receivers": [f"N{i}"]}]}
    return {"version": "1.0", "messages": [message(i) for i in range(n)],
            "nodes": [{"name": f"N{i}"} for i in range(n)],
            "comments": [{"target": {"kind": "message", "id": 0x100000 + i, "extended": True}, "text": "c"}
                         for i in range(n)],
            "environmentVars": []}


def load_seconds(n, body):
    state = lib.aletheia_init()
    start = time.process_time()
    pointer = lib.aletheia_process(state, ctypes.byref(AletheiaText(body, len(body))))
    seconds = time.process_time() - start
    answer = json.loads(ctypes.string_at(pointer).decode())
    lib.aletheia_free_str(pointer)
    lib.aletheia_close(state)
    if answer.get("status") != "success" or answer.get("warnings"):
        print(f"{n} messages: {answer.get('status')} {answer.get('message')} {answer.get('warnings')}")
        sys.exit(1)
    return seconds


bodies = {n: json.dumps({"type": "command", "command": "parseDBC", "dbc": referenced(n)}).encode()
          for n in (2500, 10000)}
times = {n: [] for n in bodies}
for _ in range(3):
    for n, body in bodies.items():
        times[n].append(load_seconds(n, body))
small, large = min(times[2500]), min(times[10000])
growth = large / small
print(f"2,500 -> 10,000 messages: {small:.3f} s -> {large:.3f} s of processor time (x{growth:.2f}, at most x9)")
if growth > 9:
    sys.exit(1)
print("PASS: a load grows linearly with its references")
PY
