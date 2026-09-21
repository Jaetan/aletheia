#!/usr/bin/env bash
# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
#
# Probes tools/mutation_run.py.
# Claim: a change to any module of the mutation harness puts every binding in
# the lane's scope. The scope rule runs all bindings when a global path
# changed, and names the harness among those paths; the harness is every
# tracked tools/mutation_*.py, since the C++ lane, its report shapes, its
# kill-route census and its slice partition were split out of the runner
# into modules of that name. A harness module the list does not cover is a
# change the lane never exercises on its own pull request: the legs decide
# they have nothing to sweep, and the change is first run on main.
# Non-zero exit: a tracked tools/mutation_*.py that no global path prefix
# covers, each named.
set -u
cd "$(dirname "$0")/.." || exit 2
py=python/.venv/bin/python
[ -x "$py" ] || exit 2
"$py" - <<'PY'
import subprocess
import sys

sys.path.insert(0, ".")
from tools.mutation_run import _GLOBAL_MUTATION_PATHS  # noqa: PLC2701

tracked = subprocess.run(
    ["git", "ls-files", "tools/mutation_*.py"], capture_output=True, text=True, check=True
).stdout.split()
uncovered = [path for path in tracked if not path.startswith(_GLOBAL_MUTATION_PATHS)]
for path in uncovered:
    print(f"{path}: a harness module no global path covers")
print(f"{len(tracked)} harness modules, {len(uncovered)} uncovered")
sys.exit(1 if uncovered else 0)
PY
