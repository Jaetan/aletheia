#!/usr/bin/env python3
"""tools/install_hooks.py — Install Aletheia's offline-CI git hooks.

Idempotent: safe to re-run.  Skips installation if the existing hook
already invokes our runner (detected by the marker comment line).

Hooks installed:
  * pre-push — runs ``tools/run_ci.py`` before allowing push.  Refuses
    push on any non-zero exit.  Rationale: limited GitHub Actions monthly
    allotment; offline validation catches breakage before it lands on
    origin.

Skip via::

    git push --no-verify

Reference: R18 cluster 1 phase 3 / memory/feedback_gate_claim_integrity.md.
"""
from __future__ import annotations

import datetime
import os
import shutil
import stat
import subprocess
import sys
from pathlib import Path

MARKER = "# aletheia-pre-push-marker (R18 cluster 1 phase 3)"

PRE_PUSH_BODY = '''\
#!/usr/bin/env python3
{marker}
"""Aletheia pre-push hook.

Runs the full offline CI sweep before allowing push.  Skip with
`git push --no-verify`.  The pre-push hook receives <remote> <url>
on argv and a list of refs being pushed on stdin.  We do not filter
by ref — every push runs the full sweep — because the gate-claim-
integrity rule requires evidence for the tip commit being pushed.
"""

import os
import subprocess
import sys
from pathlib import Path


def main() -> int:
    repo_root = subprocess.run(
        ["git", "rev-parse", "--show-toplevel"],
        capture_output=True, text=True, check=False,
    ).stdout.strip()
    if not repo_root:
        sys.stderr.write("pre-push: not in a git work tree\\n")
        return 0

    runner = Path(repo_root) / "tools" / "run_ci.py"
    if not runner.is_file():
        sys.stderr.write(f"pre-push: {{runner}} not found; skipping\\n")
        return 0

    sys.stderr.write("pre-push: running offline CI sweep (~12-15 min)...\\n")
    sys.stderr.write("pre-push: skip with `git push --no-verify` if needed\\n\\n")

    rc = subprocess.run([sys.executable, str(runner)], check=False).returncode
    if rc != 0:
        sys.stderr.write(
            "\\npre-push: CI sweep failed — push refused.\\n"
            "pre-push: review the log under tools/ci-output/, fix issues, re-push.\\n"
            "pre-push: bypass with `git push --no-verify` only when you "
            "understand why.\\n"
        )
        return 1

    sys.stderr.write("pre-push: CI sweep passed — push allowed.\\n")
    return 0


if __name__ == "__main__":
    sys.exit(main())
'''.format(marker=MARKER)


def main() -> int:
    rc = subprocess.run(
        ["git", "rev-parse", "--show-toplevel"],
        capture_output=True,
        text=True,
        check=False,
    )
    if rc.returncode != 0:
        sys.stderr.write("install-hooks: not inside a git repo\n")
        return 2
    repo_root = Path(rc.stdout.strip())
    os.chdir(repo_root)

    hooks_dir_str = subprocess.run(
        ["git", "rev-parse", "--git-path", "hooks"],
        capture_output=True,
        text=True,
        check=True,
    ).stdout.strip()
    hooks_dir = Path(hooks_dir_str)
    hooks_dir.mkdir(parents=True, exist_ok=True)

    pre_push = hooks_dir / "pre-push"
    if pre_push.is_file() and MARKER in pre_push.read_text(encoding="utf-8"):
        print(
            f"install-hooks: pre-push hook already installed (marker found at {pre_push})"
        )
        return 0

    if pre_push.is_file():
        backup = pre_push.with_suffix(
            f".aletheia-backup-{int(datetime.datetime.now().timestamp())}"
        )
        sys.stderr.write(
            f"install-hooks: existing pre-push hook backed up to {backup}\n"
        )
        shutil.copy2(pre_push, backup)

    pre_push.write_text(PRE_PUSH_BODY, encoding="utf-8")
    pre_push.chmod(pre_push.stat().st_mode | stat.S_IXUSR | stat.S_IXGRP | stat.S_IXOTH)

    print(f"install-hooks: pre-push hook installed at {pre_push}")
    print("install-hooks: every `git push` will now run `tools/run_ci.py` first")
    print("install-hooks: bypass with `git push --no-verify`")
    return 0


if __name__ == "__main__":
    sys.exit(main())
