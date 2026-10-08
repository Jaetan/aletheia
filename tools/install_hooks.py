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

  * pre-push — allows a push once ``tools/run_ci.py`` has passed on the
    tree of the commit each pushed ref names.  A recorded passing sweep of
    that tree (``tools/sweep_evidence.py``) allows it at once; otherwise the
    hook runs the sweep and allows the push only when it passed on the pushed
    tree.  git holds the remote connection open while the hook runs, so the
    sweep belongs before the push.  Rationale: offline validation catches
    breakage before it lands on origin.  The CI sweep includes the IWYU gate
    (``tools/iwyu.py``) on files modified in the branch.

Skip via::

    git commit --no-verify  # bypass pre-commit
    git push --no-verify    # bypass pre-push

These hooks exist so a gate-clean claim is backed by gate runs that observed
the committed state; bypassing them forfeits that guarantee.
"""

from __future__ import annotations

import argparse
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

Allows a push only once a full offline CI sweep has passed on what it pushes.
git connects to the remote before it runs this hook, so a sweep run here holds
that connection idle for minutes, and an idle connection that dies on the way
hangs the push.  The hook therefore first asks tools/sweep_evidence.py whether
the commit each pushed ref names (git hands them on stdin) has a passing full
sweep of its exact tree on record, and allows the push at once when it has.
When one has none, it runs the sweep here over the working tree and asks
again, so a sweep of a tree other than the pushed one allows nothing.  Skip
with `git push --no-verify`.
"""

import os
import subprocess
import sys
from pathlib import Path


def pushed_commits() -> list[str]:
    """Read the commits being pushed from the ref lines git hands on stdin.

    A line whose local id is all zeros deletes a remote ref and pushes nothing.
    """
    commits = []
    for line in sys.stdin.read().splitlines():
        fields = line.split()
        if len(fields) == 4 and fields[1].strip("0"):
            commits.append(fields[1])
    return commits


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

    for tool in ("run_ci.py", "sweep_evidence.py"):
        path = Path(repo_root) / "tools" / tool
        if not path.is_file():
            sys.stderr.write(
                f"pre-push: FAIL — {{path}} not found, so the hook cannot vouch\\n"
                "for a sweep of the pushed tree.  Push refused: this hook exists to\\n"
                "gate pushes on that sweep.  Restore the file, or use\\n"
                "`git push --no-verify` if you intend to bypass it.\\n"
            )
            return 1

    commits = pushed_commits()
    if not commits:
        sys.stderr.write("pre-push: the push sends no commit (a deletion) — push allowed.\\n")
        return 0
    evidence = [sys.executable, "-m", "tools.sweep_evidence", *commits]
    if subprocess.run(evidence, cwd=repo_root, check=False).returncode == 0:
        sys.stderr.write("pre-push: every pushed tree passed a recorded sweep — push allowed.\\n")
        return 0

    sys.stderr.write("pre-push: running the offline CI sweep (parallel lanes)...\\n")
    sys.stderr.write("pre-push: run the sweep before pushing, so the connection does not idle\\n")
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

    if subprocess.run(evidence, cwd=repo_root, check=False).returncode != 0:
        sys.stderr.write(
            "\\npre-push: the sweep passed on the working tree, which is not the tree\\n"
            "pre-push: being pushed — push refused.  Commit or stash what differs,\\n"
            "pre-push: and remove or ignore untracked files, then re-push.\\n"
        )
        return 1

    sys.stderr.write("pre-push: CI sweep passed on the pushed tree — push allowed.\\n")
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

Staged-content isolation: the tracked paths with unstaged changes and the
untracked files are recorded in a stash entry built from trees written
through private index files, then written from the index tree or removed,
so the gates see exactly what is being committed and a file that is only
staged is never written (`git stash push --keep-index` over the whole tree
checks every staged file out again, moving its mtime to the commit's time;
over a pathspec it stages the paths in the repository's index, which re-adds
a file at a staged-deleted path).  Afterwards the parked files are written
back file by file in a `finally`, from the stash's own trees and never
through a merge, so a file staged in part comes back whole.  A parking step
that fails refuses the commit; if a restore ever fails, the stash is kept
and the message says where the work is and the commands that write it back.

Then runs the `.agda` IWYU import gate (`tools/iwyu.py --check`) on the
staged `.agda` files and BLOCKS on any finding, and on a run that never
reached a verdict.  The gate queues behind a running Agda tool (`--wait-lock`)
rather than refusing to start beside it, so a commit made during a sweep
waits for the sweep instead of going through unchecked.

Bypass: `git commit --no-verify`.
"""

import os
import shutil
import subprocess
import sys
import tempfile
from pathlib import Path

_STASH_MSG = "aletheia-pre-commit-autostash"


def _run(args, cwd=None, env=None):
    # Paths come and go as the bytes git prints after `-z`: a name that is
    # not UTF-8 round-trips through surrogates instead of raising.
    return subprocess.run(
        args,
        capture_output=True,
        encoding="utf-8",
        errors="surrogateescape",
        check=False,
        cwd=cwd,
        env=env,
    )


def _git_paths(args, paths, cwd, env=None):
    # Run the git command *args* over the NUL-separated *paths*: read from
    # stdin, since the parked files can be many, and taken literally, since
    # they are file names: read as pathspecs, a `:x.txt` is magic git refuses
    # and an `x[1].txt` a pattern that names `x1.txt` too.
    return subprocess.run(
        ["git", "--literal-pathspecs", *args, "--pathspec-from-file=-", "--pathspec-file-nul"],
        input=paths,
        capture_output=True,
        encoding="utf-8",
        errors="surrogateescape",
        check=False,
        cwd=cwd,
        env=env,
    )


def _parked_paths(root):
    # What the hook parks while its gates run, two NUL-separated lists: the
    # tracked paths whose worktree copy differs from the index (edited,
    # deleted, mode changed) and the untracked files git does not ignore. A
    # nested repository, listed as `dir/`, stays where it is; a file that is
    # only staged is in neither list and is never written.
    unstaged = _run(["git", "diff", "--name-only", "-z"], cwd=root).stdout
    others = _run(["git", "ls-files", "--others", "--exclude-standard", "-z"], cwd=root).stdout
    untracked = "".join(p + "\\0" for p in others.split("\\0") if p and not p.endswith("/"))
    return unstaged, untracked


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


def _tree_after_add(root, index, paths):
    # The tree of the index file *index* once the NUL-separated *paths* are
    # added to it as they stand in the worktree (a deleted one is removed); an
    # *index* that does not exist starts empty. Written through that file, so
    # the repository's own index is never touched. Returns the tree, or None
    # with git's reason printed.
    env = {{**os.environ, "GIT_INDEX_FILE": str(index)}}
    res = _git_paths(["add"], paths, root, env) if paths else None
    if res is None or res.returncode == 0:
        res = _run(["git", "write-tree"], cwd=root, env=env)
    if res.returncode != 0:
        sys.stderr.write("\\npre-commit: could not record the parked files:\\n" + res.stderr)
        return None
    return res.stdout.strip()


def _commit_tree(root, tree, parents, subject):
    # A commit of *tree* with *parents*, or None with git's reason printed.
    args = ["git", "commit-tree", tree, "-m", subject]
    for parent in parents:
        args += ["-p", parent]
    res = _run(args, cwd=root)
    if res.returncode != 0:
        sys.stderr.write("\\npre-commit: could not record the parked files:\\n" + res.stderr)
        return None
    return res.stdout.strip()


def _create_stash(root, unstaged, untracked):
    # Park *unstaged* and *untracked* in a stash entry with the parents `git
    # stash pop` reads (first HEAD, second the index, third the untracked
    # files), built from trees written through private index files, so the
    # repository's index is never staged into and no staged file written. The
    # worktree tree records the parked paths as they stand, a deletion
    # included, which git's own does not. Returns the entry's sha, or None
    # with the reason printed.
    head = _run(["git", "rev-parse", "-q", "--verify", "HEAD"], cwd=root).stdout.strip()
    if not head:
        sys.stderr.write("\\npre-commit: no commit yet to park the unstaged changes against.\\n")
        return None
    index = os.environ.get("GIT_INDEX_FILE") or _run(
        ["git", "rev-parse", "--git-path", "index"], cwd=root
    ).stdout.strip()
    with tempfile.TemporaryDirectory() as scratch:
        work = Path(scratch) / "index"
        shutil.copy2(root / index, work)
        i_tree = _tree_after_add(root, work, "")
        w_tree = i_tree and _tree_after_add(root, work, unstaged)
        u_tree = w_tree and _tree_after_add(root, Path(scratch) / "untracked", untracked)
    if not u_tree:
        return None
    i_commit = _commit_tree(root, i_tree, [], "index for " + _STASH_MSG)
    u_commit = i_commit and _commit_tree(root, u_tree, [], "untracked files for " + _STASH_MSG)
    sha = u_commit and _commit_tree(root, w_tree, [head, i_commit, u_commit], _STASH_MSG)
    if not sha:
        return None
    stored = _run(["git", "stash", "store", "-m", _STASH_MSG, sha], cwd=root)
    if stored.returncode != 0:
        sys.stderr.write("\\npre-commit: could not store the stash entry:\\n" + stored.stderr)
        return None
    return sha


def _isolate(root, i_tree, unstaged, untracked):
    # Show the gates the staged content alone: each unstaged tracked path is
    # written from the index tree (an edit overwritten, a deletion undone),
    # each untracked file removed with the directories it leaves empty.
    # Returns whether every step succeeded.
    if unstaged:
        res = _git_paths(["restore", "--source=" + i_tree, "--worktree"], unstaged, root)
        if res.returncode != 0:
            sys.stderr.write(
                "\\npre-commit: could not write the staged content over the parked paths:\\n"
                + res.stderr
            )
            return False
    for path in untracked.split("\\0"):
        if not path:
            continue
        target = root / path
        try:
            target.unlink()
            parent = target.parent
            while parent != root and not any(parent.iterdir()):
                parent.rmdir()
                parent = parent.parent
        except OSError as exc:
            sys.stderr.write("\\npre-commit: could not set aside " + path + ": " + str(exc) + "\\n")
            return False
    return True


def _stash_paths(root, sha):
    # The paths the stash *sha* changed, NUL-separated, one list per tree the
    # restore reads: the tracked paths whose worktree content differed from
    # the index (the stash commit's tree against its index parent, every
    # status, so a deletion is listed too), and the untracked files, from the
    # third parent when the entry has one.
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
    # the commit reads it after the hook.
    if not paths:
        return None
    return _git_paths(["restore", "--source=" + source, "--worktree"], paths, root)


def _recipe(sha, tracked, untracked):
    # The commands that write the stash commit *sha* back by hand, one per
    # tree that holds parked files; the index was never changed.
    lines = [
        "pre-commit: your unstaged changes are SAFE in stash commit " + sha
        + " -- write them back with:"
    ]
    tail = " --worktree --pathspec-from-file=- --pathspec-file-nul"
    if tracked:
        lines.append(
            "pre-commit:   git diff --name-only --no-renames -z " + sha + "^2 " + sha
            + " | git --literal-pathspecs restore --source=" + sha + tail
        )
    if untracked:
        lines.append(
            "pre-commit:   git ls-tree -r -z --name-only " + sha + "^3"
            + " | git --literal-pathspecs restore --source=" + sha + "^3" + tail
        )
    return "\\n".join(lines) + "\\n"


def _restore_stash(root, sha):
    # Write the stash commit *sha*'s worktree back file by file, never merging:
    # `git stash apply` merges the stash three ways against HEAD, and a file
    # staged in part has the index's version and the stash's whole version
    # changing one region, so the apply stops unmerged after the gates passed.
    # Tracked changes come from the stash's own tree, untracked files from its
    # third parent, and a path the stash records as deleted is removed, since
    # a restore from a tree that lacks the path removes it. Returns whether
    # every file came back, printing the commands that write them back by
    # hand when one did not.
    ok = True
    tracked, untracked = _stash_paths(root, sha)
    for source, paths in ((sha, tracked), (sha + "^3", untracked)):
        res = _restore_worktree(root, source, paths)
        if res is not None and res.returncode != 0:
            sys.stderr.write(
                "\\npre-commit: FAILED to restore your unstaged changes!\\n" + res.stderr
            )
            ok = False
    if not ok:
        sys.stderr.write(_recipe(sha, tracked, untracked))
    return ok


def _drop_stash(root, sha):
    # Drop the entry *sha* by locating its ref, NOT `git stash pop`, whose
    # top a stash created concurrently during the hook could shift.
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

    unstaged, untracked = _parked_paths(root)
    stash_sha, isolated = None, True
    if unstaged or untracked:
        stash_sha = _create_stash(root, unstaged, untracked)
        isolated = bool(stash_sha) and _isolate(root, stash_sha + "^2", unstaged, untracked)

    rc = 1
    try:
        if not isolated:
            sys.stderr.write(
                "pre-commit: commit refused: the gates could not be shown the staged "
                "content alone.\\n"
            )
        else:
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
        # The entry goes once everything it held is back in place.
        if stash_sha and _restore_stash(root, stash_sha):
            _drop_stash(root, stash_sha)
    return rc


if __name__ == "__main__":
    sys.exit(main())
'''


# What each installed hook does, printed when it is installed: every tool its
# body runs is named here.
PRE_COMMIT_SUMMARY = (
    "every `git commit` runs the FAST static gates (`tools/run_ci.py --fast`) on the "
    "staged content, then `tools/iwyu.py --check` on staged `.agda` files, and blocks "
    "on failure; bypass with `--no-verify`"
)
PRE_PUSH_SUMMARY = (
    "every `git push` asks `tools/sweep_evidence.py` for a passing full sweep of the "
    "pushed tree, runs `tools/run_ci.py` when none is on record, and blocks unless a "
    "sweep of the pushed tree passed; bypass with `--no-verify`"
)


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
    argparse.ArgumentParser(description=__doc__).parse_args()  # no options; --help only
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
        PRE_COMMIT_SUMMARY,
    )
    _install_hook(
        hooks_dir,
        "pre-push",
        PRE_PUSH_BODY,
        PRE_PUSH_MARKER,
        PRE_PUSH_SUMMARY,
    )
    return 0


if __name__ == "__main__":
    sys.exit(main())
