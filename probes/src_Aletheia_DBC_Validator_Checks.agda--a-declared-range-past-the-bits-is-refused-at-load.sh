#!/usr/bin/env bash
# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
#
# Probes src/Aletheia/DBC/Validator/Checks.agda.
# Claim: a signal whose declared minimum lies below, or maximum above, every
# physical value its bits carry after scaling is an error, range_exceeds_bits,
# naming the message, the signal and the end; parseDBC and parseDBCText refuse
# the DBC with handler_validation_failed and validateDBC reports it, while a
# range that the bits carry exactly loads with neither that error nor the
# offset_scale_range warning, and a narrower range loads with the warning
# naming which way the bits reach past it. A negative factor swaps which raw
# end gives which physical end, so the cases run at a positive and a negative
# factor, signed and unsigned, past each end. Shown through the library
# itself. Non-zero exit: a range past the bits loads, an exact one is refused
# or warned, an issue names the wrong end, or the routes disagree. Exits 0
# with a note when the library is not built.
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

from aletheia.client._ffi import AletheiaText, RTSState, configure_ffi_signatures

lib = ctypes.CDLL(sys.argv[1])
configure_ffi_signatures(lib)
RTSState.acquire(lib)
state = lib.aletheia_init()


def process(command):
    body = json.dumps(command).encode()
    pointer = lib.aletheia_process(state, ctypes.byref(AletheiaText(body, len(body))))
    text = ctypes.string_at(pointer).decode()
    lib.aletheia_free_str(pointer)
    return json.loads(text)


# One 8-bit signal per case, as .dbc text: start|length@1(+ unsigned, - signed)
# (factor,offset) [minimum|maximum].  At factor 1/2 unsigned the bits carry 0
# to 127.5; at factor -1/4 offset 10 signed, raw 127 to -128 carry -21.75 to
# 42.
ABOVE = "declared maximum lies above the values its bits carry"
BELOW = "declared minimum lies below the values its bits carry"
WARN_ABOVE = "its bits carry values above the declared maximum"
WARN_BELOW = "its bits carry values below the declared minimum"
CASES = [
    ("0|8@1+ (0.5,0) [0|127.5]", set(), set()),
    ("0|8@1+ (0.5,0) [0|128]", {ABOVE}, set()),
    ("0|8@1+ (0.5,0) [-0.5|127.5]", {BELOW}, set()),
    ("0|8@1+ (0.5,0) [1|100]", set(), {WARN_ABOVE, WARN_BELOW}),
    ("0|8@1- (-0.25,10) [-21.75|42]", set(), set()),
    ("0|8@1- (-0.25,10) [-21.75|42.25]", {ABOVE}, set()),
    ("0|8@1- (-0.25,10) [-22|42]", {BELOW}, set()),
    ("0|8@1- (-0.25,10) [-21.75|41]", set(), {WARN_ABOVE}),
    ("0|8@1- (1,0) [-128|255]", {ABOVE}, set()),
]


def text_of(layout):
    return f'VERSION ""\n\nNS_ :\n\nBS_:\n\nBU_: ECU\n\nBO_ 256 M: 8 ECU\n SG_ S : {layout} "" Vector__XXX\n'


def details(issues, code, severity):
    prefix = "Message 'M', signal 'S': "
    picked = [i for i in issues if i["code"] == code and i["severity"] == severity]
    return {i["detail"].removeprefix(prefix) for i in picked if i["detail"].startswith(prefix)}, len(picked)


failures = []
for layout, errors, warnings in CASES:
    from_text = process({"type": "command", "command": "parseDBCText", "text": text_of(layout)})
    if errors:
        if from_text.get("code") != "handler_validation_failed":
            failures.append(f"{layout}: parseDBCText answered {from_text}")
            continue
        said, count = details(from_text["issues"], "range_exceeds_bits", "error")
        if said != errors or count != len(errors):
            failures.append(f"{layout}: parseDBCText named {said} ({count} issues), wanted {errors}")
        continue
    if from_text.get("status") != "success":
        failures.append(f"{layout}: parseDBCText refused a range its bits carry: {from_text}")
        continue
    said, count = details(from_text["warnings"], "offset_scale_range", "warning")
    if said != warnings or count != len(warnings):
        failures.append(f"{layout}: warned {said} ({count}), wanted {warnings}")
    dbc = from_text["dbc"]
    for route in ("parseDBC", "validateDBC"):
        answer = process({"type": "command", "command": route, "dbc": dbc})
        issues = answer.get("issues", answer.get("warnings", []))
        if answer.get("status") == "error" or any(i["code"] == "range_exceeds_bits" for i in issues):
            failures.append(f"{layout}: {route} answered {answer}")

# The JSON routes on a DBC past its bits: the text route refuses it, so it is
# built here from the exact one, its maximum raised past the bits.
exact = process({"type": "command", "command": "parseDBCText", "text": text_of(CASES[0][0])})["dbc"]
exact["messages"][0]["signals"][0]["maximum"] = 128
loaded = process({"type": "command", "command": "parseDBC", "dbc": exact})
if loaded.get("code") != "handler_validation_failed" or details(loaded["issues"], "range_exceeds_bits", "error") != ({ABOVE}, 1):
    failures.append(f"parseDBC loaded a range past the bits: {loaded}")
checked = process({"type": "command", "command": "validateDBC", "dbc": exact})
if checked.get("has_errors") is not True or details(checked.get("issues", []), "range_exceeds_bits", "error") != ({ABOVE}, 1):
    failures.append(f"validateDBC did not report the range past the bits: {checked}")

lib.aletheia_close(state)
for line in failures:
    print(line)
sys.exit(1 if failures else 0)
PY
