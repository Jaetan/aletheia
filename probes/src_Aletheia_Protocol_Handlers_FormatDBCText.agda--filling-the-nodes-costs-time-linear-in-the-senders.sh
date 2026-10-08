#!/usr/bin/env bash
# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
#
# Probes src/Aletheia/Protocol/Handlers/FormatDBCText.agda.
# Claim: formatDBCText fills an empty node list with every message's senders
# in time linear in them, up to a logarithm: the names already kept live in a
# set. 40,000 distinct senders take at most 9 times as long as 10,000 (x3 per
# doubling, the load scaling check's bound); a list of kept names grows
# 16-fold. Both are past the node bound, so each answer is the node-bound
# refusal, reached after the filling. Each time is the processor time a
# command takes, the least of three, the two sizes sent in turn: what else
# the machine runs moves wall time and leaves this nearly alone, and what
# still moves it falls on both sizes alike. Shown through the library itself.
# Non-zero exit: another answer, or the growth passes 9. Exits 0 with a note
# when the library is not built.
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
PER = 5000


def filled(total):
    signal = {"name": "S", "startBit": 0, "length": 1, "byteOrder": "little_endian", "signed": False,
              "factor": 1, "offset": 0, "minimum": 0, "maximum": 1, "unit": "", "presence": "always",
              "receivers": []}
    return {"version": "1.0", "environmentVars": [],
            "messages": [{"id": 256 + k, "name": f"M{k}", "dlc": 8, "sender": "ECU", "extended": False,
                          "signals": [signal], "senders": [f"N{k}_{i}" for i in range(PER)]}
                         for k in range(total // PER)]}


def seconds(total, body):
    state = lib.aletheia_init()
    start = time.process_time()
    pointer = lib.aletheia_process(state, ctypes.byref(AletheiaText(body, len(body))))
    elapsed = time.process_time() - start
    answer = json.loads(ctypes.string_at(pointer).decode())
    lib.aletheia_free_str(pointer)
    lib.aletheia_close(state)
    if (answer.get("field"), answer.get("observed")) != ("nodes array", total + 1):
        print(f"{total} senders answered {answer.get('code')} {answer.get('message')}")
        sys.exit(1)
    return elapsed


bodies = {total: json.dumps({"type": "command", "command": "formatDBCText", "dbc": filled(total)}).encode()
          for total in (10000, 40000)}
times = {total: [] for total in bodies}
for _ in range(3):
    for total, body in bodies.items():
        times[total].append(seconds(total, body))
small, large = min(times[10000]), min(times[40000])
growth = large / small
print(f"10,000 -> 40,000 senders: {small:.3f} s -> {large:.3f} s of processor time (x{growth:.2f}, at most x9)")
if growth > 9:
    sys.exit(1)
print("PASS: filling the nodes grows linearly with the senders")
PY
