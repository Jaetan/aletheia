#!/usr/bin/env bash
# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
#
# Probes tools/mutation_sweep_cache.py and tools/_resources.py.
# Claim: a runner launched through the prefix the C++ sweep puts on it runs
# on every CPU the sweep was given but one, and on none outside them. The
# prefix is a taskset -c, which widens an affinity as readily as it narrows
# one, so a list counted from the machine re-pins a sweep started on part of
# it onto CPUs it was never given. The probe narrows itself to the four
# highest CPUs it was given, which is neither zero-based nor the machine
# wherever it was given more than four, and reads the affinity the kernel
# hands the child rather than the list the prefix spells.
# Non-zero exit: the child ran on a CPU outside the four, or on other than
# three of them. Exits 2 without the venv, taskset, or four CPUs to narrow to.
set -u
cd "$(dirname "$0")/.." || exit 2
py=python/.venv/bin/python
[ -x "$py" ] || exit 2
command -v taskset > /dev/null || exit 2

four=$("$py" -c 'import os; print(*sorted(os.sched_getaffinity(0))[-4:], sep=",")') || exit 2
[ "$(echo "$four" | tr ',' '\n' | grep -c .)" -eq 4 ] || { echo "fewer than four CPUs to narrow to"; exit 2; }

taskset -c "$four" "$py" - << 'EOF'
import os
import subprocess
import sys

from tools.mutation_sweep_cache import polite

given = os.sched_getaffinity(0)
report = [sys.executable, "-c", "import os; print(*sorted(os.sched_getaffinity(0)))"]
child = subprocess.run(polite(report), capture_output=True, text=True, check=False)
if child.returncode != 0:
    print(f"the child did not run (exit {child.returncode}): {child.stderr.strip()}")
    sys.exit(2)
ran = {int(cpu) for cpu in child.stdout.split()}
outside = sorted(ran - given)
if outside:
    print(f"given {sorted(given)}, the runner ran on {sorted(ran)}: {outside} were never given")
    sys.exit(1)
if len(ran) != len(given) - 1:
    print(f"given {sorted(given)}, the runner ran on {sorted(ran)}, not on all of them but one")
    sys.exit(1)
print(f"PASS: given {sorted(given)}, the runner ran on {sorted(ran)}")
EOF
