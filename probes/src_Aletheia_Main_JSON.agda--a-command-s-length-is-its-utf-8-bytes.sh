#!/usr/bin/env bash
# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
#
# Probes src/Aletheia/Main/JSON.agda.
# Claim: the kernel's bound on a JSON command counts the command's UTF-8
# bytes, the size of the buffer a binding hands over, not its characters. A
# command written in two-byte characters, one byte past max-json-bytes while
# its characters number about half of it, is refused with input_length_bytes,
# observed its byte count; nothing of it is parsed. The command goes straight
# to aletheia_process, past the binding's own byte check. Shown through the
# library itself, under a 6 GiB heap. Non-zero exit: the command is accepted,
# refused another way, or observed its character count. Exits 0 with a note
# when the library is not built.
set -u
cd "$(dirname "$0")/.." || exit 2
lib=build/libaletheia-ffi.so
py=python/.venv/bin/python
[ -f "$lib" ] || { echo "kernel not built, claim untestable"; exit 0; }
[ -x "$py" ] || exit 2
ALETHEIA_RTS_OPTS=-M6G "$py" - "$lib" <<'PY'
import ctypes
import json
import sys

from aletheia.client._ffi import AletheiaText, RTSState, configure_ffi_signatures

LIMIT = 64 * 1024 * 1024
lib = ctypes.CDLL(sys.argv[1])
configure_ffi_signatures(lib)
RTSState.acquire(lib)

head = '{"type": "command", "command": "validateDBC", "dbc": {"messages": [], "environmentVars": [], "version": "'
tail = '"}}'
room = LIMIT + 1 - len(head) - len(tail)
version = "a" * (room % 2) + "é" * (room // 2)
body = (head + version + tail).encode()
characters = len(head) + len(version) + len(tail)
if len(body) != LIMIT + 1:
    print(f"the probe built {len(body)} bytes, not {LIMIT + 1}")
    sys.exit(2)

state = lib.aletheia_init()
pointer = lib.aletheia_process(state, ctypes.byref(AletheiaText(body, len(body))))
answer = json.loads(ctypes.string_at(pointer).decode())
lib.aletheia_free_str(pointer)
lib.aletheia_close(state)
got = {key: answer.get(key) for key in ("code", "bound_kind", "observed", "limit")}
want = {"code": "input_bound_exceeded", "bound_kind": "input_length_bytes", "observed": LIMIT + 1, "limit": LIMIT}
if got != want:
    print(f"{len(body)} bytes in {characters} characters answered {got}, not {want}")
    sys.exit(1)
print(f"PASS: {len(body)} bytes in {characters} characters refused as {len(body)} bytes")
PY
