#!/usr/bin/env bash
# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
#
# Probes src/Aletheia/DBC/Bounds.agda.
# Claim: parseDBC, validateDBC and formatDBCText refuse a DBC past any of its
# size bounds the same way, before anything else runs: code
# input_bound_exceeded, the bound's kind, the observed count one past the
# limit, the limit, the field that crossed it, and the message
# "<Command>: <field>: <kind label> <observed> exceeds limit <limit>". Every
# list and text bound is crossed once, alone; a DBC exactly at a bound loads;
# with two bounds crossed, the first in the documented order is the one
# refused; formatDBCText refuses the node list it fills from the senders when
# that list passes the node bound; parseDBCText refuses a text whose DBC is
# past a bound the same way. The value-description total is not crossed here:
# reaching it takes a million entries, whose JSON alone exhausts the default
# heap. Shown through the library itself. Non-zero exit: a DBC past a bound is
# accepted, refused with another code, kind, count, field or message, or a DBC
# within its bounds is refused. Exits 0 with a note when the library is not
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

from aletheia.client._ffi import AletheiaText, RTSState, configure_ffi_signatures

lib = ctypes.CDLL(sys.argv[1])
configure_ffi_signatures(lib)
RTSState.acquire(lib)

TEXT = 65536
LONG = "x" * (TEXT + 1)
LONGER = "y" * (TEXT + 2)
COMMANDS = {"parseDBC": "ParseDBC", "validateDBC": "ValidateDBC", "formatDBCText": "FormatDBCText"}
LABELS = {"array_cardinality": "array cardinality", "string_length": "string length"}


def process(command):
    body = json.dumps(command).encode()
    state = lib.aletheia_init()
    pointer = lib.aletheia_process(state, ctypes.byref(AletheiaText(body, len(body))))
    answer = json.loads(ctypes.string_at(pointer).decode())
    lib.aletheia_free_str(pointer)
    lib.aletheia_close(state)
    return answer


def signal(name, unit="", **more):
    base = {"name": name, "startBit": 0, "length": 1, "byteOrder": "little_endian", "signed": False,
            "factor": 1, "offset": 0, "minimum": 0, "maximum": 1, "unit": unit,
            "presence": "always", "receivers": []}
    base.update(more)
    return base


def message(i, signals=(), extended=False, **more):
    base = {"id": i, "name": f"M{i}", "dlc": 8, "sender": "ECU", "extended": extended,
            "signals": list(signals)}
    base.update(more)
    return base


def dbc(**over):
    base = {"version": "1.0", "messages": [message(256, [signal("S")])], "environmentVars": []}
    base.update(over)
    return base


def messages(n):
    return [message(0x100000 + i, extended=True) for i in range(n)]


def signals(n):
    return [message(256, [signal(f"S{i}") for i in range(n)])]


def attributes(n):
    return [{"kind": "definition", "name": f"A{i}", "scope": "network", "attrType": {"kind": "string"}}
            for i in range(n)]


def comments(n, text="c"):
    return [{"target": {"kind": "network"}, "text": text} for _ in range(n)]


def mux(n):
    selected = signal("S", startBit=8)
    del selected["presence"]
    selected.update(multiplexor="Mx", multiplex_values=list(range(n)))
    return [message(256, [signal("Mx", length=8, maximum=255), selected])]


# (field, kind, limit, the DBC one past it, the DBC exactly at it)
BOUNDS = [
    ("messages array", "array_cardinality", 10000, lambda n: dbc(messages=messages(n))),
    ("signals array", "array_cardinality", 1024, lambda n: dbc(messages=signals(n))),
    ("senders array", "array_cardinality", 10000,
     lambda n: dbc(messages=[message(256, [signal("S")], senders=[f"N{i}" for i in range(n)])])),
    ("receivers array", "array_cardinality", 10000,
     lambda n: dbc(messages=[message(256, [signal("S", receivers=[f"N{i}" for i in range(n)])])])),
    ("multiplex values array", "array_cardinality", 1024, lambda n: dbc(messages=mux(n))),
    ("attributes array", "array_cardinality", 10000, lambda n: dbc(attributes=attributes(n))),
    ("enum labels array", "array_cardinality", 10000,
     lambda n: dbc(attributes=[{"kind": "definition", "name": "A", "scope": "network",
                                "attrType": {"kind": "enum", "values": [f"v{i}" for i in range(n)]}}])),
    ("comments array", "array_cardinality", 10000, lambda n: dbc(comments=comments(n))),
    ("nodes array", "array_cardinality", 10000, lambda n: dbc(nodes=[{"name": f"N{i}"} for i in range(n)])),
    ("value tables array", "array_cardinality", 10000,
     lambda n: dbc(valueTables=[{"name": f"T{i}", "entries": []} for i in range(n)])),
    ("signal groups array", "array_cardinality", 10000,
     lambda n: dbc(signalGroups=[{"name": f"G{i}", "signals": []} for i in range(n)])),
    ("signal group members array", "array_cardinality", 1024,
     lambda n: dbc(signalGroups=[{"name": "G", "signals": [f"S{i}" for i in range(n)]}])),
    ("environment variables array", "array_cardinality", 10000,
     lambda n: dbc(environmentVars=[{"name": f"E{i}", "varType": 0, "initial": 0, "minimum": 0, "maximum": 1}
                                    for i in range(n)])),
    ("unresolved value descriptions array", "array_cardinality", 10000,
     lambda n: dbc(unresolvedValueDescs=[{"id": 999, "extended": False, "signalName": "Q", "entries": []}
                                         for _ in range(n)])),
    ("version string", "string_length", TEXT, lambda n: dbc(version="x" * n)),
    ("signal text field", "string_length", TEXT,
     lambda n: dbc(messages=[message(256, [signal("S", unit="x" * n)])])),
    ("comment text", "string_length", TEXT, lambda n: dbc(comments=comments(1, "x" * n))),
    ("attribute text field", "string_length", TEXT,
     lambda n: dbc(attributes=[{"kind": "definition", "name": "A", "scope": "network",
                                "attrType": {"kind": "enum", "values": ["x" * n]}}])),
    ("value table label", "string_length", TEXT,
     lambda n: dbc(valueTables=[{"name": "T", "entries": [{"value": 0, "description": "x" * n}]}])),
    ("unresolved value description label", "string_length", TEXT,
     lambda n: dbc(unresolvedValueDescs=[{"id": 999, "extended": False, "signalName": "Q",
                                          "entries": [{"value": 0, "description": "x" * n}]}])),
]

# Two bounds crossed: the first one named is the one refused.
ORDER = [
    ("messages array", 10001, dbc(version=LONG, messages=messages(10001))),
    ("signals array", 1025, dbc(messages=signals(1025), attributes=attributes(10001))),
    ("comments array", 10001, dbc(comments=comments(10001), nodes=[{"name": f"N{i}"} for i in range(10001)])),
    ("version string", TEXT + 1, dbc(version=LONG, comments=comments(1, LONGER))),
    ("signal text field", TEXT + 1,
     dbc(messages=[message(256, [signal("S", unit=LONG, valueDescriptions=[{"value": 0, "description": LONGER}])])])),
    ("comment text", TEXT + 2,
     dbc(comments=comments(1, LONGER), attributes=[{"kind": "definition", "name": "A", "scope": "network",
                                                     "attrType": {"kind": "enum", "values": [LONG]}}])),
]

failures = []


def expect_refusal(command, payload, field, kind, observed, limit, where):
    answer = process({"type": "command", "command": command, **payload})
    want = {
        "status": "error", "code": "input_bound_exceeded", "field": field, "bound_kind": kind,
        "observed": observed, "limit": limit,
        "message": f"{COMMANDS.get(command, 'ParseDBCText')}: {field}: {LABELS[kind]} {observed} exceeds limit {limit}",
    }
    got = {key: answer.get(key) for key in want}
    if got != want:
        failures.append(f"{where}, {command}: {got}")


def expect_accepted(command, payload, where):
    answer = process({"type": "command", "command": command, **payload})
    if answer.get("code") == "input_bound_exceeded":
        failures.append(f"{where}, {command}: refused a DBC within its bounds: {answer.get('message')}")


for field, kind, limit, build in BOUNDS:
    over = build(limit + 1)
    for command in COMMANDS:
        expect_refusal(command, {"dbc": over}, field, kind, limit + 1, limit, f"{field} one past")
    expect_accepted("validateDBC", {"dbc": build(limit)}, f"{field} at the limit")

for field, observed, payload in ORDER:
    kind = "string_length" if field.endswith(("string", "field", "text", "label")) else "array_cardinality"
    limit = TEXT if kind == "string_length" else (1024 if field == "signals array" else 10000)
    for command in COMMANDS:
        expect_refusal(command, {"dbc": payload}, field, kind, observed, limit, f"two bounds, {field} first")

# formatDBCText fills an empty node list with the senders: ECU and 2 x 5001.
filled = dbc(messages=[message(256, [signal("S")], senders=[f"A{i}" for i in range(5001)]),
                       message(257, [signal("S")], senders=[f"B{i}" for i in range(5001)])])
expect_accepted("parseDBC", {"dbc": filled}, "filled nodes")
expect_refusal("formatDBCText", {"dbc": filled}, "nodes array", "array_cardinality", 10003, 10000, "filled nodes")

# parseDBCText: the same refusal, from text.
head = 'VERSION "{v}"\n\nNS_ :\n\nBS_:\n\nBU_: ECU\n\nBO_ 256 M: 8 ECU\n SG_ S : 0|1@1+ (1,0) [0|1] "" ECU\n\n'
texts = [
    ("version string", "string_length", TEXT + 1, TEXT, head.format(v=LONG)),
    ("senders array", "array_cardinality", 10001, 10000,
     head.format(v="1.0") + "BO_TX_BU_ 256 : " + ",".join(f"N{i}" for i in range(10001)) + ";\n"),
]
for field, kind, observed, limit, text in texts:
    expect_refusal("parseDBCText", {"text": text}, field, kind, observed, limit, f"text, {field}")

if failures:
    for line in failures:
        print(line)
    sys.exit(1)
print(f"PASS: {len(BOUNDS)} bounds refused alike by {len(COMMANDS)} commands and accepted at their limits,"
      f" {len(ORDER)} orders, the filled nodes, {len(texts)} texts")
PY
