#!/usr/bin/env bash
# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
#
# Probes README.md, the comment above the streaming example.
# Claim: the field list the comment gives for CANFrameTuple is the tuple's own
# field list, in order, as python/aletheia/client/_types.py declares it. The
# comment used to name the first field timestamp_us where the tuple names it
# timestamp.
# Non-zero exit: the comment's field list differs from the tuple's.
set -u
cd "$(dirname "$0")/.." || exit 2
py=python/.venv/bin/python
[ -x "$py" ] || exit 2
PYTHONPATH=python "$py" - <<'PY'
import re, sys
from aletheia.client._types import CANFrameTuple
text = open("README.md", encoding="utf-8").read()
m = re.search(r"CANFrameTuple\(([^)]*)\)", text)
if not m:
    print("README.md has no CANFrameTuple(...) field list"); sys.exit(1)
stated = [f.strip() for f in re.sub(r"\n#\s*", " ", m.group(1)).split(",")]
fields = list(CANFrameTuple._fields)
if stated != fields:
    print(f"README.md lists {stated}, the tuple declares {fields}"); sys.exit(1)
print(f"PASS: the comment names the tuple's {len(fields)} fields in order")
PY
