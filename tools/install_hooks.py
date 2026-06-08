# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
"""tools/install_hooks.py — Install Aletheia's offline-CI git hooks.

Idempotent: safe to re-run.  Each hook is installed only if not already
marked installed (detected by a hook-specific marker comment line).

Hooks installed:
  * pre-commit — runs ``tools/iwyu.py --check`` (the single scope-aware
    `.agdai` IWYU tool) on staged .agda files as an ADVISORY check.  Prints
    any finding (dead / redundant / narrowable / unresolved import), but
    exits 0 so the commit proceeds.  It is not sub-second (it warm-loads the
    staged files to refresh their interfaces), so it runs only when .agda
    files are staged; the blocking gate runs at pre-push.

  * pre-push — runs ``tools/run_ci.py`` before allowing push.  Refuses
    push on any non-zero exit.  Rationale: limited GitHub Actions monthly
    allotment; offline validation catches breakage before it lands on
    origin.  The CI sweep includes the IWYU gate (``tools/iwyu.py``) on
    files modified in the branch.

Skip via::

    git commit --no-verify  # bypass pre-commit
    git push --no-verify    # bypass pre-push

Reference: memory/feedback_gate_claim_integrity.md.
"""

from __future__ import annotations

import os
import shutil
import stat
import subprocess
import sys
from datetime import UTC, datetime
from pathlib import Path

from tools._common import emit, find_executable

PRE_PUSH_MARKER = "# aletheia-pre-push-marker (offline CI sweep)"
PRE_COMMIT_MARKER = "# aletheia-pre-commit-marker (IWYU reader advisory)"

PRE_PUSH_BODY = f'''\
#!/usr/bin/env python3.14
{PRE_PUSH_MARKER}
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

    rc = subprocess.run(
        [sys.executable, "-m", "tools.run_ci"], cwd=repo_root, check=False
    ).returncode
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
'''


PRE_COMMIT_BODY = f'''\
#!/usr/bin/env python3.14
{PRE_COMMIT_MARKER}
"""Aletheia pre-commit hook — IWYU import advisory.

For each staged .agda file under src/, runs the single scope-aware
`.agdai` IWYU tool (`tools/iwyu.py --check`) and prints any finding
(dead / redundant / narrowable / unresolved import) as a warning.
Always exits 0; the commit proceeds whether findings exist or not.

Rationale:
  - The `.agdai` reader is the project's trusted import-resolution tool;
    the regex scanner and recompile-confirm approaches are retired.  It
    is not sub-second (it warm-loads the staged files to refresh their
    interfaces), so this advisory runs only when .agda files are staged.
  - The blocking gate runs at pre-push via tools/run_ci.py (step 9:
    `iwyu --check --diff` on the branch diff).  If a finding slips past
    this advisory, pre-push catches it.

Bypass: `git commit --no-verify`.
"""

import subprocess
import sys
from pathlib import Path


def main() -> int:
    repo_root = subprocess.run(
        ["git", "rev-parse", "--show-toplevel"],
        capture_output=True, text=True, check=False,
    ).stdout.strip()
    if not repo_root:
        return 0
    repo_root = Path(repo_root)
    src = repo_root / "src"

    # Staged .agda files under src/ (Added / Copied / Modified / Renamed).
    diff = subprocess.run(
        ["git", "diff", "--cached", "--name-only",
         "--diff-filter=ACMR", "--", "src/*.agda"],
        capture_output=True, text=True, check=False,
    )
    rels = []
    for p in diff.stdout.splitlines():
        path = repo_root / p.strip()
        if p.strip() and path.is_file():
            try:
                rels.append(str(path.relative_to(src)))
            except ValueError:
                continue
    if not rels:
        return 0  # no staged Agda under src/ — nothing to check

    # Advisory: `--check` exits 1 on findings, but the commit always proceeds.
    result = subprocess.run(
        [sys.executable, "-m", "tools.iwyu", "--check", *rels],
        capture_output=True, text=True, check=False, cwd=repo_root,
    )
    if result.returncode != 0:
        sys.stderr.write(
            "\\npre-commit: IWYU flagged imports in staged .agda files:\\n\\n"
        )
        sys.stderr.write(result.stdout.strip() + "\\n\\n")
        sys.stderr.write(
            "pre-commit: ADVISORY ONLY — commit proceeds.  The pre-push gate\\n"
            "(tools/run_ci.py) blocks on these.  Remove a DEAD named import; fix\\n"
            "wildcard `open import M` via `python -m tools.iwyu --apply`.\\n\\n"
        )
    return 0


if __name__ == "__main__":
    sys.exit(main())
'''


def _install_hook(
    hooks_dir: Path,
    name: str,
    body: str,
    marker: str,
    description: str,
) -> bool:
    """Install the named hook, returning whether it was (re)written.

    Returns True if newly installed (or re-installed because the marker was
    missing), False if the hook is already current.
    """
    path = hooks_dir / name
    if path.is_file() and marker in path.read_text(encoding="utf-8"):
        emit(f"install-hooks: {name} already installed (marker found at {path})")
        return False
    if path.is_file():
        ts = int(datetime.now(UTC).timestamp())
        backup = path.with_suffix(f".aletheia-backup-{ts}")
        sys.stderr.write(f"install-hooks: existing {name} hook backed up to {backup}\n")
        shutil.copy2(path, backup)
    path.write_text(body, encoding="utf-8")
    path.chmod(path.stat().st_mode | stat.S_IXUSR | stat.S_IXGRP | stat.S_IXOTH)
    emit(f"install-hooks: {name} hook installed at {path}")
    emit(f"install-hooks:   {description}")
    return True


def main() -> int:
    """Install the pre-commit and pre-push hooks, returning a process exit code."""
    git = find_executable("git")
    rc = subprocess.run(
        [git, "rev-parse", "--show-toplevel"],
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
        [git, "rev-parse", "--git-path", "hooks"],
        capture_output=True,
        text=True,
        check=True,
    ).stdout.strip()
    hooks_dir = Path(hooks_dir_str)
    hooks_dir.mkdir(parents=True, exist_ok=True)

    _install_hook(
        hooks_dir,
        "pre-commit",
        PRE_COMMIT_BODY,
        PRE_COMMIT_MARKER,
        "every `git commit` will run `tools/iwyu.py --check` on staged "
        + ".agda files (advisory only — never blocks)",
    )
    _install_hook(
        hooks_dir,
        "pre-push",
        PRE_PUSH_BODY,
        PRE_PUSH_MARKER,
        "every `git push` will run `tools/run_ci.py` first; bypass with `--no-verify`",
    )
    return 0


if __name__ == "__main__":
    sys.exit(main())
