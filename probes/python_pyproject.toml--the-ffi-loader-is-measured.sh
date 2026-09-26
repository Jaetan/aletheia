#!/usr/bin/env bash
# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
#
# Probes python/pyproject.toml.
# Claim: the coverage configuration measures the FFI loader, which the suite
# runs against the built kernel, and omits only the install receipt `shake
# install` generates, which no checkout carries. The omit list was once
# wider, holding the loader out as unreachable from tests, which a
# measurement showed false.
# Non-zero exit: the omit list names a tracked file, or names anything but
# the install receipt.
set -u
cd "$(dirname "$0")/.." || exit 2

python/.venv/bin/python - <<'PY' || exit 1
import subprocess
import sys
import tomllib
from pathlib import Path

config = tomllib.loads(Path("python/pyproject.toml").read_text(encoding="utf-8"))
omit = config["tool"]["coverage"]["run"]["omit"]
if omit != ["aletheia/_install_config.py"]:
    print(f"the omit list is {omit}, want the install receipt alone")
    sys.exit(1)
tracked = subprocess.run(
    ["git", "ls-files", "--", "python/aletheia"], check=True, capture_output=True, text=True
).stdout.split()
held_out = [f for f in tracked if f.removeprefix("python/") in omit]
if held_out:
    print(f"the omit list holds out a tracked file: {held_out}")
    sys.exit(1)
if "python/aletheia/client/_ffi.py" not in tracked:
    print("the FFI loader is not where this probe expects it")
    sys.exit(1)
PY
exit 0
