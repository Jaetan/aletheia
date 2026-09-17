#!/usr/bin/env bash
# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
#
# Probes go/aletheia/backend.go against go/aletheia/ffi.go.
# Claim: the two frame builders take one slice of injections, not a count
# beside three slices of that length. The three used to be parallel arrays
# whose equal length no type carried, so the boundary checked it by hand and
# answered a mismatch with a refusal naming the three lengths. One slice of a
# three-field struct carries the property instead, and the check is gone.
# The shape is what is checked, by reading the declarations: the property the
# change buys is that a mismatch cannot be written, so there is no behaviour to
# drive. The split into three C arrays is allowed to exist in exactly one file,
# the one that talks to C, and this checks that too.
# Non-zero exit: a count or a parallel array is back on the interface, or the
# split has spread beyond the cgo file.
set -u
cd "$(dirname "$0")/.." || exit 2
py=python/.venv/bin/python
[ -x "$py" ] || exit 2

"$py" - <<'PY'
import re
import subprocess
import sys

backend = open("go/aletheia/backend.go", encoding="utf-8").read()
bad = []

for method in ("BuildFrameBin", "UpdateFrameBin"):
    match = re.search(rf"^\t{method}\((.*)\) \(\[\]byte, error\)$", backend, re.M)
    if match is None:
        bad.append(f"the interface no longer declares {method} answering a payload")
        continue
    params = match.group(1)
    if "[]SignalInjection" not in params:
        bad.append(f"{method} does not take a slice of injections: {params}")
    for leaked in ("numSignals", "[]uint32", "[]int64"):
        if leaked in params:
            bad.append(f"{method} carries {leaked}, which the injection slice replaced: {params}")

if "type SignalInjection struct" not in backend:
    bad.append("backend.go no longer declares SignalInjection")

# The three parallel arrays are the C entry point's shape and belong to the one
# file that talks to C.
elsewhere = subprocess.run(
    ["git", "grep", "-l", "signalArrays\\|signalArrayPtrs", "--", "go/"],
    capture_output=True, text=True, check=False).stdout.split()
unexpected = [p for p in elsewhere if p not in ("go/aletheia/ffi.go",)]
if unexpected:
    bad.append("the split into parallel arrays appears outside the cgo file: " + ", ".join(unexpected))

if bad:
    print("the frame builders no longer take one slice:")
    for line in bad:
        print(f"  {line}")
    sys.exit(1)
print("PASS: both frame builders take one slice of injections, split into arrays only at the C boundary")
PY
