#!/usr/bin/env bash
# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
#
# Probes probes/cpp_.clang-tidy--the-gate-fails-on-a-discarded-return.sh.
# Claim: while one run of the probe holds its lock, a second run reports the
# lock as held, names the holder, and touches no source. Two runs that
# overlapped would each capture the other's injection as its own original and
# write it back as the restore. The lock is held here, the probe is run, and
# its refusal read; the three injected sources are compared before and after.
# Non-zero exit: 1 when the probe ran on under the held lock, refused without
# naming the holder, or changed a source; 2 when the lock could not be taken,
# or the toolchain the probed probe needs is absent, in which case it too
# exits 2.
set -u
cd "$(dirname "$0")/.." || exit 2
probe=probes/cpp_.clang-tidy--the-gate-fails-on-a-discarded-return.sh
command -v run-clang-tidy-23 > /dev/null || { echo "run-clang-tidy-23 not installed"; exit 0; }
[ -f cpp/build/compile_commands.json ] || { echo "no compile database; configure cpp/build"; exit 2; }
python/.venv/bin/python - "$probe" <<'PY'
import fcntl
import os
import subprocess
import sys
from pathlib import Path

probe = sys.argv[1]
lock_path = Path("cpp/build/probe-scratch/clang-tidy-injection.lock")
lock_path.parent.mkdir(parents=True, exist_ok=True)
fd = os.open(lock_path, os.O_CREAT | os.O_RDWR, 0o644)
try:
    fcntl.flock(fd, fcntl.LOCK_EX | fcntl.LOCK_NB)
except BlockingIOError:
    print(f"another run holds {lock_path}; the probe cannot stage its contention")
    raise SystemExit(2)
os.ftruncate(fd, 0)
os.write(fd, f"{os.getpid()}\n".encode())

sources = [
    Path("cpp/src/types.cpp"),
    Path("cpp/tests/unit_tests_dbc.cpp"),
    Path("cpp/benchmarks/stability_bench.cpp"),
]
before = [s.read_bytes() for s in sources]
run = subprocess.run(["bash", probe], capture_output=True, text=True, check=False)
after = [s.read_bytes() for s in sources]
out = run.stdout + run.stderr
bad = []
if run.returncode != 2:
    bad.append(f"the probe exited {run.returncode}, not 2, while its lock was held")
if f"another run of this probe holds {lock_path} (pid {os.getpid()})" not in out:
    bad.append("the refusal does not name this probe as the holder")
if before != after:
    bad.append("a source changed under the refused run")
if bad:
    print("a second run of the probe does not refuse the way it should:")
    for line in bad:
        print(f"  {line}")
    print(out[-800:])
    raise SystemExit(1)
print(f"PASS: the probe reported its lock held by pid {os.getpid()} and touched nothing")
PY
