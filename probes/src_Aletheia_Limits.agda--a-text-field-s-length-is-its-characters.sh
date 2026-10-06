#!/usr/bin/env bash
# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
#
# Probes src/Aletheia/Limits.agda.
# Claim: a DBC text field's bound, max-string-length-characters, counts the
# field's characters, as its name says. A version string of 65,536 two-byte
# characters (131,072 UTF-8 bytes) is within it; one of 65,537 is refused with
# string_length, observed 65,537. Shown through the library itself (validateDBC).
# Non-zero exit: the constant is absent from the kernel, or the bound counts
# anything but characters. Exits 0 with a note when the library is not built.
set -u
cd "$(dirname "$0")/.." || exit 2
grep -q '^max-string-length-characters = 65536$' src/Aletheia/Limits.agda || {
	echo "src/Aletheia/Limits.agda defines no max-string-length-characters = 65536"
	exit 1
}
lib=build/libaletheia-ffi.so
py=python/.venv/bin/python
[ -f "$lib" ] || { echo "kernel not built, claim untestable"; exit 0; }
[ -x "$py" ] || exit 2
"$py" - "$lib" <<'PY'
import ctypes
import json
import sys

from aletheia.client._ffi import AletheiaText, RTSState, configure_ffi_signatures

lib = ctypes.CDLL(sys.argv[1])
configure_ffi_signatures(lib)
RTSState.acquire(lib)


def validate(version):
    body = json.dumps({"type": "command", "command": "validateDBC",
                       "dbc": {"version": version, "messages": [], "environmentVars": []}},
                      ensure_ascii=False).encode()
    state = lib.aletheia_init()
    pointer = lib.aletheia_process(state, ctypes.byref(AletheiaText(body, len(body))))
    answer = json.loads(ctypes.string_at(pointer).decode())
    lib.aletheia_free_str(pointer)
    lib.aletheia_close(state)
    return answer


failures = []
within = validate("é" * 65536)
if within.get("status") != "validation":
    failures.append(f"65,536 characters (131,072 bytes) refused: {within}")
past = validate("é" * 65537)
got = {key: past.get(key) for key in ("code", "bound_kind", "observed", "limit", "field")}
want = {"code": "input_bound_exceeded", "bound_kind": "string_length", "observed": 65537,
        "limit": 65536, "field": "version string"}
if got != want:
    failures.append(f"65,537 characters answered {got}, not {want}")
for line in failures:
    print(line)
if failures:
    sys.exit(1)
print("PASS: 65,536 two-byte characters are within the bound, 65,537 are refused as 65,537")
PY
