#!/usr/bin/env bash
# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
#
# Probes cpp/.clang-format.
# Claim: the file lists only the values the project decides, and the effective
# configuration that produces is the one recorded here. Cutting a restated
# default is behaviour-neutral only while the base style keeps giving that
# value, so the whole dumped configuration is pinned rather than the file's own
# lines: a base-style change that moves any option is caught at the next run
# instead of being absorbed silently.
#
# When this fails after a toolchain bump, read the diff it prints. An option
# that moved for a good reason is accepted by recording the new digest here,
# in a commit that says which option moved and why that is wanted.
# Non-zero exit: the effective configuration is not the recorded one, or a key
# the file sets merely restates the base style.
set -eu
root=$(git rev-parse --show-toplevel)
cd "$root/cpp"
# The binary the gate runs: the venv-pinned clang-format, never the system one.
cf="$root/python/.venv/bin/clang-format"
[ -x "$cf" ] || exit 2
py="$root/python/.venv/bin/python"
[ -x "$py" ] || py=python3

expected=f60007f6fbec9d4cf84ee06061de48fbf8b913fbf44841a21ecc5d7bbc3cced7
actual=$("$cf" --dump-config | sha256sum | cut -d' ' -f1)
if [ "$actual" != "$expected" ]; then
    echo "FAIL: the effective format configuration is not the recorded one"
    echo "  recorded $expected"
    echo "  measured $actual"
    "$cf" --dump-config > /tmp/aletheia-clang-format-now.yaml
    echo "  the configuration now in force is in /tmp/aletheia-clang-format-now.yaml"
    exit 1
fi

ALETHEIA_CLANG_FORMAT="$cf" "$py" - <<'PY'
import os
import re
import subprocess
import sys

CF = os.environ["ALETHEIA_CLANG_FORMAT"]


def blocks(args):
    """Top-level option name to its whole value, nested lines included."""
    text = subprocess.run(args, capture_output=True, text=True, check=True).stdout
    out, key = {}, None
    for line in text.split("\n"):
        if line.startswith("---") or not line.strip():
            continue
        m = re.match(r"^([A-Za-z0-9_]+):(.*)$", line)
        if m:
            key = m.group(1)
            out[key] = [m.group(2).strip()]
        elif key and line[:1] in (" ", "\t"):
            out[key].append(line)
    return {k: "\n".join(v) for k, v in out.items()}


mine = blocks([CF, "--dump-config"])
base = blocks([CF, "--style=LLVM", "--dump-config"])
own = [
    m.group(1)
    for m in (re.match(r"^([A-Za-z0-9_]+):", l) for l in open(".clang-format", encoding="utf-8"))
    if m and m.group(1) not in ("Language", "BasedOnStyle")
]
restated = [k for k in own if k in base and mine.get(k) == base.get(k)]
if restated:
    print("FAIL: these keys restate the base style: " + " ".join(restated))
    sys.exit(1)
print(f"PASS: the effective configuration is the recorded one and all {len(own)} keys decide something")
PY
