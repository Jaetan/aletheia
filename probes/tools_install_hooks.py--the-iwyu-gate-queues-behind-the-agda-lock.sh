#!/usr/bin/env bash
# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
#
# Probes tools/install_hooks.py, the pre-commit hook body it installs.
# Claim: while another Agda tool holds the agda-tree lock, the hook's IWYU
# gate waits for it rather than failing or passing, and once the lock is
# released it runs the real tool to a verdict. The lock refusal exits non-zero
# with its reason on stderr and nothing on stdout; the hook once printed its
# "flagged imports" header over that empty report and let the commit through,
# so a commit made during a sweep was told its imports were flagged and went
# in unchecked. The probe holds the lock itself, runs the rendered hook's gate
# over one real source file with only the staged-file listing faked, checks
# that the gate is still waiting after a few seconds, releases the lock, and
# checks that the gate then returns zero.
# Non-zero exit: 1 when the gate returned while the lock was held, or did not
# return zero once it was released; 2 when the probe could not take the lock
# or find its toolchain.
set -u
cd "$(dirname "$0")/.." || exit 2
py=python/.venv/bin/python
[ -x "$py" ] || exit 2

"$py" - <<'PY'
import fcntl
import os
import subprocess
import sys
import threading
import types
from pathlib import Path

root = Path.cwd()
fd = os.open(root / ".agda-tree.lock", os.O_CREAT | os.O_RDWR, 0o644)
try:
    fcntl.flock(fd, fcntl.LOCK_EX | fcntl.LOCK_NB)
except BlockingIOError:
    print("another Agda tool holds .agda-tree.lock; the probe cannot stage its contention")
    raise SystemExit(2)
os.ftruncate(fd, 0)
os.write(fd, str(os.getpid()).encode())

from tools.install_hooks import PRE_COMMIT_BODY  # noqa: E402

module = types.ModuleType("aletheia_pre_commit_under_probe")
exec(compile(PRE_COMMIT_BODY, "<pre-commit>", "exec"), vars(module))
hook = vars(module)
real_run = hook["_run"]
staged = "src/Aletheia/Prelude.agda"
assert (root / staged).is_file(), staged


def run(args, cwd=None):
    if args[:2] == ["git", "diff"]:
        return subprocess.CompletedProcess(args, 0, staged + "\n", "")
    return real_run(args, cwd=cwd)


hook["_run"] = run
# The tool's stderr is inherited, so route this process's stderr to a file:
# the line the wait branch prints is the evidence of contention, where a gate
# that is merely slow to start would also find the lock free.
logs = root / "tools" / "ci-output" / "probes"
logs.mkdir(parents=True, exist_ok=True)
captured = logs / "tools_install_hooks.py--the-iwyu-gate-queues-behind-the-agda-lock.stderr"
sys.stderr.flush()
os.dup2(os.open(captured, os.O_CREAT | os.O_WRONLY | os.O_TRUNC, 0o644), 2)
result = []
gate = threading.Thread(target=lambda: result.append(hook["_iwyu_gate"](root)))
gate.start()
gate.join(5)
if not gate.is_alive():
    print(f"the gate returned {result} while the lock was held: it neither waited nor was refused")
    sys.exit(1)
os.close(fd)  # releases the lock; the gate's tool should now run to a verdict
gate.join(300)
if gate.is_alive():
    print("the gate did not return within 300 s of the lock's release")
    sys.exit(1)
if result != [0]:
    print(f"the gate returned {result} on a clean file once the lock was released")
    sys.exit(1)
waited = f"waiting for .agda-tree.lock, held by another Agda tool (pid {os.getpid()}"
if waited not in captured.read_text(encoding="utf-8"):
    print("the gate passed, but its tool never said it was waiting for the lock this probe held:")
    print(captured.read_text(encoding="utf-8"))
    sys.exit(1)
print("PASS: the gate waited for the lock this probe held and passed the clean file once it was released")
PY
