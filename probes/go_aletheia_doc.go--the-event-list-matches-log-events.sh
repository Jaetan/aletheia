#!/usr/bin/env bash
# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
#
# Probes go/aletheia/doc.go.
# Claim: the log event table in the package documentation names exactly the
# events docs/LOG_EVENTS.yaml pins, each at the level the YAML gives it, and
# each emitted by the source the table names (rts.cores_mismatch by the
# FFIBackend in ffi.go, every other event by the Client in client.go).
# Non-zero exit: an event is in one list and not the other, a level differs,
# or a named emitter does not carry the event string.
set -u
cd "$(dirname "$0")/.." || exit 2
py=python/.venv/bin/python
[ -x "$py" ] || exit 2
"$py" - <<'PY'
import re
import sys

import yaml

doc = open("go/aletheia/doc.go", encoding="utf-8").read()
rows = re.findall(r"^//\t([a-z_.]+)\s+\((Client|FFIBackend), (Warn|Info|Debug)\)$", doc, re.M)
if not rows:
    print("no event table found in doc.go")
    sys.exit(1)
spec = yaml.safe_load(open("docs/LOG_EVENTS.yaml", encoding="utf-8"))
pinned = {e["name"]: e["level"] for e in spec["events"]}
bad = []
listed = {name for name, _, _ in rows}
for name in sorted(pinned.keys() - listed):
    bad.append(f"{name} is pinned in LOG_EVENTS.yaml and missing from doc.go")
for name in sorted(listed - pinned.keys()):
    bad.append(f"{name} is listed in doc.go and not pinned in LOG_EVENTS.yaml")
emitter_file = {"Client": "go/aletheia/client.go", "FFIBackend": "go/aletheia/ffi.go"}
for name, emitter, level in rows:
    if name in pinned and pinned[name] != level.lower():
        bad.append(f"{name}: doc.go says {level}, LOG_EVENTS.yaml says {pinned[name]}")
    src = open(emitter_file[emitter], encoding="utf-8").read()
    if f'"{name}"' not in src:
        bad.append(f"{name}: doc.go names {emitter} as the emitter but {emitter_file[emitter]} never logs it")
for line in bad:
    print(line)
if bad:
    sys.exit(1)
print(f"PASS: the {len(rows)} events in doc.go are the ones LOG_EVENTS.yaml pins, at its levels, from the emitters named")
PY
