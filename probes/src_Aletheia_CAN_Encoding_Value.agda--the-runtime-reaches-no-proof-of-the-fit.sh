#!/usr/bin/env bash
# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
#
# Probes src/Aletheia/CAN/Encoding/Value.agda.
# Claim: the proofs the frame builder and the loader rest on are used by the
# runtime only in erased positions, so no compiled code the shim reaches
# imports them. Starting from the generated modules haskell-shim/src imports,
# the closure of the generated Haskell's imports reaches the encoding layer
# (Aletheia.CAN.Encoding.Value) and never the proof that an encodable raw value
# fits its bits (Aletheia.CAN.Encoding.Properties.Fits), the raw range's
# arithmetic it rests on (Aletheia.CAN.Encoding.Arithmetic.Range), or the
# validity theorem and its parts (Aletheia.DBC.Validity.Theorem, Composition,
# ErrorChecks, WarningChecks). Read from build/MAlonzo, which the build
# writes. Non-zero exit: 1 when a proof module is reached or the encoding
# layer is not; 2 when the generated code cannot be read. Exits 0 with a note
# when the build has not run.
set -u
cd "$(dirname "$0")/.." || exit 2
py=python/.venv/bin/python
[ -x "$py" ] || exit 2
[ -d build/MAlonzo/Code/Aletheia ] || { echo "no generated Haskell, claim untestable"; exit 0; }
"$py" - <<'PY'
import os
import re
import sys

ROOT = "build/MAlonzo/Code"
IMPORT = re.compile(r"^import\s+(?:qualified\s+)?(MAlonzo\.Code\.[\w.']+)", re.M)


def generated(module):
    return os.path.join(ROOT, *module.split(".")[2:]) + ".hs"


seeds = set()
for directory, _, files in os.walk("haskell-shim/src"):
    for name in files:
        if name.endswith((".hs", ".hsc")):
            with open(os.path.join(directory, name), encoding="utf-8") as source:
                seeds |= set(IMPORT.findall(source.read()))
if not seeds:
    print("the shim imports no generated module: the closure cannot be read")
    sys.exit(2)

reached, pending = set(), list(seeds)
while pending:
    module = pending.pop()
    if module in reached:
        continue
    reached.add(module)
    path = generated(module)
    if os.path.exists(path):
        with open(path, encoding="utf-8") as source:
            pending.extend(IMPORT.findall(source.read()))

prefix = "MAlonzo.Code.Aletheia."
must_reach = ["CAN.Encoding.Value"]
must_not = [
    "CAN.Encoding.Properties.Fits",
    "CAN.Encoding.Arithmetic.Range",
    "DBC.Validity.Theorem",
    "DBC.Validity.Composition",
    "DBC.Validity.ErrorChecks",
    "DBC.Validity.WarningChecks",
]
failures = [f"{m} is not reached" for m in must_reach if prefix + m not in reached]
failures += [f"{m} is reached by the runtime" for m in must_not if prefix + m in reached]
for line in failures:
    print(line)
sys.exit(1 if failures else 0)
PY
