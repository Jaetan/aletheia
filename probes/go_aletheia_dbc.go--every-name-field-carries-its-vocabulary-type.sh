#!/usr/bin/env bash
# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
#
# Probes go/aletheia/dbc.go.
# Claim: every field of the DBC records that holds a signal's, a message's or a
# node's name carries the vocabulary type the package defines for it, and the
# two comment targets carry the identifier as the package's own type rather
# than as a number beside a flag. The package typed the fields a reader meets
# first and left the rest as strings, so half the names were typed and half
# were not, and a comment could name a message no frame could carry.
# Three names stay strings because the package defines no type for them: a
# signal group's, a value table's and an environment variable's. They are
# listed here so that a type added for one of them is noticed rather than
# quietly left out.
# The identifier pair stays on the four attribute targets, which the ruling
# scoped out; that asymmetry is deliberate and is stated here so the next round
# reads it as a decision rather than an oversight.
# Non-zero exit: a name field has gone back to a raw type, or a comment target
# has gone back to the pair.
set -u
cd "$(dirname "$0")/.." || exit 2
py=python/.venv/bin/python
[ -x "$py" ] || exit 2

"$py" - <<'PY'
import re
import sys

src = open("go/aletheia/dbc.go", encoding="utf-8").read()
bad = []

# field name -> the type it must carry, keyed by the struct it belongs to.
WANT = {
    "DBCSignal": {"Receivers": "[]NodeName"},
    "DBCMessage": {"Senders": "[]NodeName"},
    "DBCNode": {"Name": "NodeName"},
    "DBCRawValueDesc": {"SignalName": "SignalName", "ID": "CANID"},
    "DBCCommentTargetNode": {"Node": "NodeName"},
    "DBCCommentTargetMessage": {"ID": "CANID"},
    "DBCCommentTargetSignal": {"ID": "CANID", "Signal": "SignalName"},
    "DBCAttrTargetNode": {"Node": "NodeName"},
    "DBCAttrTargetSignal": {"Signal": "SignalName"},
    "DBCAttrTargetNodeMsg": {"Node": "NodeName"},
    "DBCAttrTargetNodeSig": {"Node": "NodeName", "Signal": "SignalName"},
}
# Names with no vocabulary type, left as strings by the same ruling.
UNTYPED = {"DBCSignalGroup": "Name", "DBCValueTable": "Name", "DBCEnvironmentVar": "Name"}

for struct, fields in WANT.items():
    match = re.search(rf"^type {struct} struct \{{\n(.*?)^\}}", src, re.M | re.S)
    if match is None:
        bad.append(f"{struct} is no longer a struct in this file")
        continue
    body = match.group(1)
    for field, want in fields.items():
        found = re.search(rf"^\t{field}\s+(\S+)", body, re.M)
        if found is None:
            bad.append(f"{struct} has no field {field}")
        elif found.group(1) != want:
            bad.append(f"{struct}.{field} is {found.group(1)}, not {want}")

for struct, field in UNTYPED.items():
    match = re.search(rf"^type {struct} struct \{{\n(.*?)^\}}", src, re.M | re.S)
    if match is None:
        continue
    found = re.search(rf"^\t{field}\s+(\S+)", match.group(1), re.M)
    if found is not None and found.group(1) != "string":
        bad.append(f"{struct}.{field} is {found.group(1)} now, so this probe's list of untyped names is stale")

# The two comment targets must not carry the flag the identifier type replaced.
for struct in ("DBCCommentTargetMessage", "DBCCommentTargetSignal"):
    match = re.search(rf"^type {struct} struct \{{\n(.*?)^\}}", src, re.M | re.S)
    if match and "Extended" in match.group(1):
        bad.append(f"{struct} carries Extended again, which the identifier type replaced")

if bad:
    print("the DBC records no longer carry their vocabulary types:")
    for line in bad:
        print(f"  {line}")
    sys.exit(1)
print(f"PASS: {sum(len(v) for v in WANT.values())} fields across {len(WANT)} records carry their types")
PY
