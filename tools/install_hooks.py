#!/usr/bin/env python3
"""tools/install_hooks.py — Install Aletheia's offline-CI git hooks.

Idempotent: safe to re-run.  Each hook is installed only if not already
marked installed (detected by a hook-specific marker comment line).

Hooks installed:
  * pre-commit — runs ``tools/scan_dead_imports.py`` on staged .agda files
    as an ADVISORY check.  Prints findings if any, but exits 0 so the
    commit proceeds.  The regex scanner has a non-trivial false-positive
    rate (mixfix syntax sugar, sections, public re-exports — see
    ``memory/feedback_agda_import_pruning_safety.md``); blocking commits
    on its output would be too noisy.  The precise gate runs at pre-push.

  * pre-push — runs ``tools/run_ci.py`` before allowing push.  Refuses
    push on any non-zero exit.  Rationale: limited GitHub Actions monthly
    allotment; offline validation catches breakage before it lands on
    origin.  The CI sweep includes the precise ``prune_unused_imports.py
    --check-only`` gate on files modified in the branch.

Skip via::

    git commit --no-verify  # bypass pre-commit
    git push --no-verify    # bypass pre-push

Reference: R18 cluster 1 phase 3 / memory/feedback_gate_claim_integrity.md.
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

PRE_PUSH_MARKER = "# aletheia-pre-push-marker (R18 cluster 1 phase 3)"
PRE_COMMIT_MARKER = "# aletheia-pre-commit-marker (dead-import scanner)"

PRE_PUSH_BODY = f'''\
#!/usr/bin/env python3
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
#!/usr/bin/env python3
{PRE_COMMIT_MARKER}
"""Aletheia pre-commit hook — fast dead-import scanner (advisory).

For each staged .agda file, runs the regex scanner and prints findings
as a warning.  Always exits 0; the commit proceeds whether findings
exist or not.

Rationale:
  - Pre-commit must be fast (sub-second target).  The regex scanner
    meets this; the precise agda-driven tool (5-15 min/file) does not.
  - The regex scanner has FPs (mixfix syntax sugar, sections, public
    re-exports — see memory/feedback_agda_import_pruning_safety.md).
    Blocking commits on noisy output erodes developer trust in the
    hook system.
  - The precise gate runs at pre-push via tools/run_ci.py.  If a real
    dead import slipped past pre-commit, pre-push catches it.

Bypass: `git commit --no-verify`.
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
        return 0
    repo_root = Path(repo_root)

    scanner = repo_root / "tools" / "scan_dead_imports.py"
    if not scanner.is_file():
        # Tool not present (perhaps an old branch); silently skip.
        return 0

    # Get staged .agda files (Added / Copied / Modified / Renamed).
    diff = subprocess.run(
        ["git", "diff", "--cached", "--name-only",
         "--diff-filter=ACMR", "--", "*.agda"],
        capture_output=True, text=True, check=False,
    )
    files = [
        repo_root / p.strip()
        for p in diff.stdout.splitlines()
        if p.strip() and (repo_root / p.strip()).is_file()
    ]
    if not files:
        return 0  # no Agda changes — nothing to check

    # Run the scanner.  Exit code is always 0; we only care about output.
    result = subprocess.run(
        [sys.executable, "-m", "tools.scan_dead_imports", "--summary"]
        + [str(f) for f in files],
        capture_output=True, text=True, check=False, cwd=repo_root,
    )
    out = result.stdout.strip()
    # If nothing was flagged, the scanner prints only its totals line
    # ("Total: 0 dead candidates...").  Suppress that case.
    has_findings = "Total: 0 dead" not in out
    if has_findings:
        sys.stderr.write(
            "\\npre-commit: dead-import scanner found candidates in staged .agda files:\\n\\n"
        )
        sys.stderr.write(out + "\\n\\n")
        sys.stderr.write(
            "pre-commit: ADVISORY ONLY — commit proceeds.  Run\\n"
            "  tools/prune_unused_imports.py --check-only "
            + " ".join(str(f.relative_to(repo_root)) for f in files) + "\\n"
            "to verify which are actually dead (the scanner has known FPs:\\n"
            "see memory/feedback_agda_import_pruning_safety.md).\\n\\n"
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
        "every `git commit` will run `tools/scan_dead_imports.py` on staged "
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
