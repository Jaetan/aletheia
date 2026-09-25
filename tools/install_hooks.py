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
    Then runs ``tools/iwyu.py --check`` on the staged .agda files as a
    BLOCKING import gate, queued behind a running Agda tool rather than
    refused beside it.

  * pre-push — runs ``tools/run_ci.py`` before allowing push.  Refuses
    push on any non-zero exit.  Rationale: limited GitHub Actions monthly
    allotment; offline validation catches breakage before it lands on
    origin.  The CI sweep includes the IWYU gate (``tools/iwyu.py``) on
    files modified in the branch.

Skip via::

    git commit --no-verify  # bypass pre-commit
    git push --no-verify    # bypass pre-push

These hooks exist so a gate-clean claim is backed by gate runs that observed
the committed state; bypassing them forfeits that guarantee.
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
PRE_COMMIT_MARKER = "# aletheia-pre-commit-marker (FAST static gate + IWYU gate)"

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
    # A hook that cannot run the sweep must BLOCK, not wave the push through:
    # letting it pass would enforce nothing while looking like it had.
    # `git push --no-verify` remains the deliberate, visible escape.
    if not repo_root:
        sys.stderr.write("pre-push: FAIL — not in a git work tree; cannot run the CI sweep\\n")
        return 1

    runner = Path(repo_root) / "tools" / "run_ci.py"
    if not runner.is_file():
        sys.stderr.write(
            f"pre-push: FAIL — {{runner}} not found, so the CI sweep did not run.\\n"
            "Push refused: this hook exists to gate pushes on that sweep, and it\\n"
            "cannot vouch for a sweep it never ran.  Restore the runner, or use\\n"
            "`git push --no-verify` if you intend to bypass it.\\n"
        )
        return 1

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
"""Aletheia pre-commit hook — FAST static gate + IWYU import gate, both blocking.

Runs the compile-free FAST tier of the CI sweep (`tools/run_ci.py --fast`:
per-binding format checks, SPDX / review-mark / venv hygiene, ruff, pylint)
against the STAGED content and BLOCKS the commit on any failure — so a
non-conforming commit fails in seconds, before it exists, instead of minutes
later at pre-push.  The full sweep still runs at pre-push.

Staged-content isolation: unstaged + untracked changes are stashed
(`--keep-index --include-untracked`) so the gates see exactly what is being
committed, then written back file by file in a `finally`, from the stash's
own trees and never through a merge, so a file staged in part comes back
whole.  The stash is named; if a restore ever fails, the message says where
the work is and the commands that write it back.

Then runs the `.agda` IWYU import gate (`tools/iwyu.py --check`) on the
staged `.agda` files and BLOCKS on any finding, and on a run that never
reached a verdict.  The gate queues behind a running Agda tool (`--wait-lock`)
rather than refusing to start beside it, so a commit made during a sweep
waits for the sweep instead of going through unchecked.

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


def _run_iwyu(rels, cwd):
    # stdout captured (the report is the verdict), stderr left on the terminal
    # so the tool's own progress and refusals are read live: "waiting for the
    # agda-tree lock" during a sweep, a traceback when it crashes.
    return subprocess.run(
        [sys.executable, "-m", "tools.iwyu", "--check", "--wait-lock", *rels],
        stdout=subprocess.PIPE,
        text=True,
        check=False,
        cwd=cwd,
    )


def _iwyu_gate(root):
    # Run the .agdai IWYU reader over every staged .agda under src/; return the
    # hook's exit code.  A run that found something prints its report on stdout.
    # A non-zero exit with nothing on stdout is a run that never happened (a
    # usage error, a crash before the report), and that blocks too: a gate
    # that could not run vouches for nothing.
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
        return 0
    sys.stderr.write(
        "pre-commit: IWYU import gate on " + str(len(rels)) + " staged .agda file(s) "
        "(queues behind a running Agda tool)...\\n"
    )
    res = _run_iwyu(rels, root)
    if res.returncode == 0:
        return 0
    if not res.stdout.strip():
        sys.stderr.write(
            "\\npre-commit: IWYU could not run on the staged .agda files (exit "
            + str(res.returncode) + "); its own output is above.  Commit refused: "
            "this hook cannot vouch for a check it never got.  Reproduce with "
            "`python -m tools.iwyu --check " + " ".join(rels) + "`.\\n\\n"
        )
        return 1
    sys.stderr.write("\\npre-commit: IWYU flagged imports in staged .agda files:\\n\\n")
    sys.stderr.write(res.stdout.strip() + "\\n\\n")
    sys.stderr.write(
        "pre-commit: commit refused.  Remove a DEAD named import; fix wildcard "
        "`open import M` via `python -m tools.iwyu --apply`.\\n\\n"
    )
    return 1


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


def _stash_paths(root, sha):
    # The paths the stash *sha* changed, NUL-separated, one list per tree the
    # restore reads: the tracked paths whose worktree content differed from
    # the index (the stash commit's tree against its index parent, every
    # status, so a deletion is listed too), and the untracked files, which sit
    # in a third parent git makes only when there were any.
    tracked = _run(
        ["git", "diff", "--name-only", "--no-renames", "-z", sha + "^2", sha], cwd=root
    ).stdout
    untracked = ""
    if _run(["git", "rev-parse", "-q", "--verify", sha + "^3"], cwd=root).returncode == 0:
        untracked = _run(
            ["git", "ls-tree", "-r", "-z", "--name-only", sha + "^3"], cwd=root
        ).stdout
    return tracked, untracked


def _restore_worktree(root, source, paths):
    # Write the worktree files under *paths* from the tree *source*, file by
    # file: a path the tree lacks is removed. The index is not touched, since
    # the commit reads it after the hook. The pathspecs go in on stdin, not
    # argv, because a stash can carry a whole build tree.
    if not paths:
        return None
    return subprocess.run(
        [
            "git",
            "restore",
            "--source=" + source,
            "--worktree",
            "--pathspec-from-file=-",
            "--pathspec-file-nul",
        ],
        input=paths,
        capture_output=True,
        text=True,
        check=False,
        cwd=root,
    )


def _restore_stash(root, sha):
    # Write the stash commit *sha*'s worktree back file by file, never merging:
    # `git stash apply` merges the stash three ways against HEAD, and a file
    # staged in part has the index's version and the stash's whole version
    # changing one region, so the apply stops unmerged after the gates passed.
    # Tracked changes come from the stash's own tree, untracked files from its
    # third parent, and a path the stash records as deleted is removed, since
    # a restore from a tree that lacks the path removes it. Then drop the entry
    # by locating its ref, NOT `git stash pop`, whose top a stash created
    # concurrently during the hook could shift.
    tracked, untracked = _stash_paths(root, sha)
    for source, paths in ((sha, tracked), (sha + "^3", untracked)):
        res = _restore_worktree(root, source, paths)
        if res is not None and res.returncode != 0:
            sys.stderr.write(
                "\\npre-commit: FAILED to restore your unstaged changes!\\n"
                "pre-commit: they are SAFE in stash commit " + sha + " -- write them back with:\\n"
                "pre-commit:   git diff --name-only --no-renames -z " + sha + "^2 " + sha
                + " | git restore --source=" + sha
                + " --worktree --pathspec-from-file=- --pathspec-file-nul\\n"
                "pre-commit:   git ls-tree -r -z --name-only " + sha + "^3"
                + " | git restore --source=" + sha
                + "^3 --worktree --pathspec-from-file=- --pathspec-file-nul\\n"
                + res.stderr
            )
            return
    listing = _run(["git", "stash", "list", "--format=%gd %H"], cwd=root).stdout
    for line in listing.splitlines():
        parts = line.split()
        if len(parts) == 2 and parts[1] == sha:
            _run(["git", "stash", "drop", parts[0]], cwd=root)
            break


def main() -> int:
    # A hook that cannot run the FAST tier must BLOCK, not wave the commit
    # through: passing would enforce nothing while looking like it had.
    # `git commit --no-verify` remains the deliberate, visible escape.
    root = _run(["git", "rev-parse", "--show-toplevel"]).stdout.strip()
    if not root:
        sys.stderr.write("pre-commit: FAIL — not in a git work tree; FAST gates did not run\\n")
        return 1
    root = Path(root)
    if not (root / "tools" / "run_ci.py").is_file():
        sys.stderr.write(
            "pre-commit: FAIL — tools/run_ci.py not found, so the FAST gates did not run.\\n"
            "Commit refused: this hook cannot vouch for gates it never ran.  Restore\\n"
            "the runner, or use `git commit --no-verify` to bypass deliberately.\\n"
        )
        return 1

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
        if rc != 0:
            sys.stderr.write(
                "\\npre-commit: FAST static gates failed — commit refused.\\n"
                "pre-commit: fix the reported format/lint/hygiene issues, or bypass "
                "with `git commit --no-verify`.\\n"
            )
        else:
            rc = _iwyu_gate(root)
    finally:
        if stash_sha:
            _restore_stash(root, stash_sha)
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
