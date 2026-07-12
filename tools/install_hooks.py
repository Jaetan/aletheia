# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
"""tools/install_hooks.py — Install Aletheia's offline-CI git hooks.

Idempotent: safe to re-run.  Each hook is installed only if not already
marked installed (detected by a hook-specific marker comment line).

Hooks installed:
  * pre-commit — runs the FAST tier of the CI sweep (``tools/run_ci.py
    --fast``: per-binding format checks, SPDX / review-mark / venv hygiene,
    ruff, pylint) against the STAGED content and BLOCKS the commit on any
    failure, so a non-conforming commit fails in seconds rather than minutes
    later at pre-push.  Unstaged + untracked changes are stashed for the
    duration so the gates see exactly what is being committed, then restored.
    Also runs ``tools/iwyu.py --check`` on staged .agda files as a non-blocking
    ADVISORY (prints findings, never blocks).

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
PRE_COMMIT_MARKER = "# aletheia-pre-commit-marker (FAST static gate + IWYU advisory)"

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

    sys.stderr.write("pre-push: running offline CI sweep (parallel lanes; ~5-8 min)...\\n")
    sys.stderr.write("pre-push: skip with `git push --no-verify` if needed\\n\\n")

    # --parallel runs the lanes concurrently (memory-safe heavy_limit=2 default);
    # tune with ALETHEIA_CI_HEAVY_LIMIT.  Falls back to serial semantics on a
    # single core.  The local sweep also benefits from the incremental build (the
    # `build` prereq recompiles only changed MAlonzo modules).
    rc = subprocess.run(
        [sys.executable, "-m", "tools.run_ci", "--parallel"], cwd=repo_root, check=False
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
"""Aletheia pre-commit hook — FAST static gate (blocking) + IWYU advisory.

Runs the compile-free FAST tier of the CI sweep (`tools/run_ci.py --fast`:
per-binding format checks, SPDX / review-mark / venv hygiene, ruff, pylint)
against the STAGED content and BLOCKS the commit on any failure — so a
non-conforming commit fails in seconds, before it exists, instead of minutes
later at pre-push.  The full sweep still runs at pre-push.

Staged-content isolation: unstaged + untracked changes are stashed
(`--keep-index --include-untracked`) so the gates see exactly what is being
committed, then restored in a `finally`.  The stash is named; if a restore
ever fails, the message says where the work is (recoverable via `git stash`).
Every FAST gate is non-mutating (`--check` / `--dry-run`), so the pop never
conflicts with the check itself.

Also runs the `.agda` IWYU import check as a non-blocking advisory.

Bypass: `git commit --no-verify`.
"""

import subprocess
import sys
from pathlib import Path

_STASH_MSG = "aletheia-pre-commit-autostash"


def _run(args, cwd=None):
    return subprocess.run(args, capture_output=True, text=True, check=False, cwd=cwd)


def _has_worktree_changes(root):
    # Anything to isolate? Unstaged tracked changes (diff vs the index) OR
    # untracked, non-ignored files.  If not, the worktree already equals the
    # staged content and no stash is needed.
    if _run(["git", "diff", "--quiet"], cwd=root).returncode != 0:
        return True
    others = _run(["git", "ls-files", "--others", "--exclude-standard"], cwd=root).stdout
    return bool(others.strip())


def _iwyu_advisory(root):
    # For each staged .agda under src/, run the .agdai IWYU reader as a WARNING.
    diff = _run(
        ["git", "diff", "--cached", "--name-only", "--diff-filter=ACMR", "--", "src/*.agda"],
        cwd=root,
    )
    src = root / "src"
    rels = []
    for line in diff.stdout.splitlines():
        p = root / line.strip()
        if line.strip() and p.is_file():
            try:
                rels.append(str(p.relative_to(src)))
            except ValueError:
                continue
    if not rels:
        return
    res = _run([sys.executable, "-m", "tools.iwyu", "--check", *rels], cwd=root)
    if res.returncode != 0:
        sys.stderr.write("\\npre-commit: IWYU flagged imports in staged .agda files:\\n\\n")
        sys.stderr.write(res.stdout.strip() + "\\n\\n")
        sys.stderr.write(
            "pre-commit: ADVISORY ONLY — commit proceeds.  Remove a DEAD named "
            "import; fix wildcard `open import M` via `python -m tools.iwyu --apply`.\\n\\n"
        )


def _create_stash(root):
    # Park unstaged + untracked changes (keeping the index) and return the exact
    # stash COMMIT sha we created — so restore targets THAT commit regardless of
    # stack order or git's locale.  Called only when _has_worktree_changes() is
    # True, so `git stash push` always produces a stash on success (no need to
    # parse the human "No local changes to save" string, which a localized git
    # would translate).
    res = _run(
        ["git", "stash", "push", "--keep-index", "--include-untracked", "-m", _STASH_MSG],
        cwd=root,
    )
    if res.returncode != 0:
        sys.stderr.write(
            "pre-commit: could not stash unstaged changes; checking the "
            "working tree as-is:\\n" + res.stderr
        )
        return None
    sha = _run(["git", "rev-parse", "-q", "--verify", "stash@{{0}}"], cwd=root).stdout.strip()
    return sha or None


def _restore_stash(root, sha):
    # Restore exactly the stash commit *sha* — NOT `git stash pop`, which pops the
    # top of the stack (a stash created concurrently during the hook could shift
    # it).  Apply by sha, then drop the matching entry by locating its ref.
    app = _run(["git", "stash", "apply", sha], cwd=root)
    if app.returncode != 0:
        sys.stderr.write(
            "\\npre-commit: FAILED to restore your unstaged changes!\\n"
            "pre-commit: they are SAFE in stash commit " + sha + " — recover with:\\n"
            "pre-commit:   git stash apply " + sha + "\\n" + app.stderr
        )
        return
    listing = _run(["git", "stash", "list", "--format=%gd %H"], cwd=root).stdout
    for line in listing.splitlines():
        parts = line.split()
        if len(parts) == 2 and parts[1] == sha:
            _run(["git", "stash", "drop", parts[0]], cwd=root)
            break


def main() -> int:
    root = _run(["git", "rev-parse", "--show-toplevel"]).stdout.strip()
    if not root:
        return 0
    root = Path(root)
    if not (root / "tools" / "run_ci.py").is_file():
        sys.stderr.write("pre-commit: tools/run_ci.py not found; skipping\\n")
        return 0

    stash_sha = _create_stash(root) if _has_worktree_changes(root) else None

    rc = 1
    try:
        sys.stderr.write(
            "pre-commit: FAST static gates on staged content "
            "(seconds; skip with `git commit --no-verify`)...\\n"
        )
        rc = subprocess.run(
            [sys.executable, "-m", "tools.run_ci", "--fast"], cwd=root, check=False
        ).returncode
        if rc == 0:
            _iwyu_advisory(root)
    finally:
        if stash_sha:
            _restore_stash(root, stash_sha)

    if rc != 0:
        sys.stderr.write(
            "\\npre-commit: FAST static gates failed — commit refused.\\n"
            "pre-commit: fix the reported format/lint/hygiene issues, or bypass "
            "with `git commit --no-verify`.\\n"
        )
    return rc


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

    Content-aware (NOT just marker-presence): skips only when the on-disk hook is
    byte-identical to the current template, so a template change (e.g. adding
    ``--parallel``) refreshes an already-installed hook instead of being silently
    skipped. Any DIFFERING hook — whether our own stale one or a foreign one — is
    backed up before being overwritten, so no local edit is ever lost. Returns True
    if newly installed / refreshed, False if already current.
    """
    path = hooks_dir / name
    if path.is_file():
        current = path.read_text(encoding="utf-8")
        if current == body:
            emit(f"install-hooks: {name} already installed and current ({path})")
            return False
        # Content differs — back up before overwriting, whether this is our own
        # stale hook (template changed) or a foreign one, so no local edit is lost.
        ts = int(datetime.now(UTC).timestamp())
        backup = path.with_suffix(f".aletheia-backup-{ts}")
        sys.stderr.write(f"install-hooks: existing {name} hook backed up to {backup}\n")
        shutil.copy2(path, backup)
        if marker in current:
            emit(f"install-hooks: refreshing stale {name} hook (template changed)")
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
        "every `git commit` runs the FAST static gates (`run_ci.py --fast`) on "
        + "staged content and blocks on failure; bypass with `--no-verify`",
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
