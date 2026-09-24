#!/usr/bin/env bash
# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
#
# Probes tools/check_limits_parity.py.
# Claim: the parity gate holds the C++ mirror to the Agda source of truth, so
# a value that drifts there is refused. The header is drifted in a scratch copy
# of the working tree, so the tree itself is never written: a sweep, a hook or
# a commit reading it meanwhile would take the drift for the user's change.
# Non-zero exit: the gate passes on a drifted C++ value, the refusal does not
# name the C++ mirror, or the gate does not pass on the tree as it stands.
# Exits 2 without the virtual environment.
set -u
cd "$(dirname "$0")/.." || exit 2
py=$PWD/python/.venv/bin/python
[ -x "$py" ] || exit 2

work=$(mktemp -d) || exit 2
tree=$work/tree
trap 'git worktree remove --force "$tree" > /dev/null 2>&1; rm -rf "$work"' EXIT
# The checkout is HEAD; the diff carries what is edited and not yet committed,
# since the probe must read the tree as it stands.
git worktree add -q --detach "$tree" HEAD || exit 2
git diff --no-ext-diff --no-color --binary --src-prefix=a/ --dst-prefix=b/ HEAD |
    git -C "$tree" apply --index --allow-empty || exit 2
"$py" - "$tree" <<'PY'
import subprocess
import sys
from pathlib import Path

tree = Path(sys.argv[1])
header = tree / "cpp/include/aletheia/limits.hpp"
gate = [sys.executable, "-m", "tools.check_limits_parity"]
original = header.read_text(encoding="utf-8")
needle = "inline constexpr std::uint64_t max_nesting_depth = 64;"
if needle not in original:
    print("the constant the probe drifts is not in the header")
    raise SystemExit(2)

clean = subprocess.run(gate, cwd=tree, capture_output=True, text=True, check=False)
if clean.returncode != 0:
    print(f"the gate refuses the tree as it stands: {clean.stderr}")
    raise SystemExit(1)
if "C++" not in clean.stdout:
    print(f"the gate's summary does not name the C++ mirror: {clean.stdout}")
    raise SystemExit(1)

header.write_text(original.replace(needle, needle.replace("= 64;", "= 63;")), encoding="utf-8")
drifted = subprocess.run(gate, cwd=tree, capture_output=True, text=True, check=False)

if drifted.returncode == 0:
    print("a drifted C++ value was accepted")
    raise SystemExit(1)
if "C++ max-constant" not in drifted.stderr:
    print(f"the refusal is not about the C++ mirror: {drifted.stderr}")
    raise SystemExit(1)
PY
