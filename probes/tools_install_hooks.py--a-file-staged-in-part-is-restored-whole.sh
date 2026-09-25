#!/usr/bin/env bash
# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
#
# Probes tools/install_hooks.py, the pre-commit hook body it installs.
# Claim: a commit of half a file's hunks lands the half, and the hook writes
# the worktree back whole. The hook parks unstaged and untracked changes while
# its gates run; a restore that merges the parked tree three ways against the
# partial index stops unmerged on the region both sides changed, after the
# gates have passed, and the commit fails with the tree half applied. The
# probe builds a scratch repository whose gate runner passes at once, installs
# the rendered hook, stages one hunk of a file and leaves a second in the
# tree beside an unstaged deletion and an untracked file, commits, and reads
# back the commit, the worktree and the stash list. The caller's global git
# configuration is shut out, so a signing setting there cannot stop the
# commit on a passphrase. An optional first argument names the hook source
# to render from, in place of the tree's own.
# Non-zero exit: 1 when the commit failed, landed more than the staged hunk,
# or left the worktree short of what it held before; 2 when the scratch
# repository could not be made or the toolchain is missing.
set -u
cd "$(dirname "$0")/.." || exit 2
py=python/.venv/bin/python
[ -x "$py" ] || exit 2
src=${1:-tools/install_hooks.py}
[ -f "$src" ] || exit 2
work=$(mktemp -d) || exit 2
trap 'rm -rf "$work"' EXIT

"$py" - "$src" "$work" <<'PY'
import importlib.util
import os
import stat
import subprocess
import sys
from pathlib import Path

src, work = Path(sys.argv[1]), Path(sys.argv[2])
spec = importlib.util.spec_from_file_location("install_hooks_under_probe", src)
module = importlib.util.module_from_spec(spec)
spec.loader.exec_module(module)
body = module.PRE_COMMIT_BODY.split("\n", 1)[1]

env = {**os.environ, "GIT_CONFIG_GLOBAL": os.devnull, "GIT_CONFIG_NOSYSTEM": "1"}
repo = work / "repo"
repo.mkdir()


def git(*args, check=True):
    return subprocess.run(
        ["git", *args], cwd=repo, env=env, capture_output=True, text=True, check=check
    )


try:
    git("init", "-q")
    git("config", "user.name", "hook probe")
    git("config", "user.email", "hook@probe")
    (repo / "tools").mkdir()
    (repo / "tools" / "__init__.py").write_text("", encoding="utf-8")
    (repo / "tools" / "run_ci.py").write_text("raise SystemExit(0)\n", encoding="utf-8")
    (repo / "notes.txt").write_text("l1\nl2\nl3\nl4\nl5\nl6\n", encoding="utf-8")
    (repo / "gone.txt").write_text("gone\n", encoding="utf-8")
    git("add", ".")
    git("commit", "-q", "-m", "base")
except (subprocess.CalledProcessError, OSError) as exc:
    print(f"the scratch repository could not be made: {exc}")
    raise SystemExit(2)

hook = repo / ".git" / "hooks" / "pre-commit"
hook.write_text("#!" + sys.executable + "\n" + body, encoding="utf-8")
hook.chmod(hook.stat().st_mode | stat.S_IXUSR)

staged_notes = "l1\nL2\nl3\nl4\nl5\nl6\n"
whole_notes = "l1\nL2\nL3\nl4\nl5\nl6\n"
(repo / "notes.txt").write_text(staged_notes, encoding="utf-8")
git("add", "notes.txt")
(repo / "notes.txt").write_text(whole_notes, encoding="utf-8")
(repo / "gone.txt").unlink()
(repo / "scratch.txt").write_text("scratch\n", encoding="utf-8")
staged = git("diff", "--cached").stdout

commit = git("commit", "-q", "-m", "half", check=False)
bad = []
if commit.returncode != 0:
    bad.append(f"the commit failed with exit {commit.returncode}")
elif git("show", "HEAD:notes.txt").stdout != staged_notes:
    bad.append("the commit does not hold the staged hunk alone")
elif git("diff", "HEAD~1", "HEAD").stdout != staged:
    bad.append("the commit's diff is not what was staged")
if (repo / "notes.txt").read_text(encoding="utf-8") != whole_notes:
    bad.append("the worktree file is not whole")
if (repo / "gone.txt").exists():
    bad.append("the unstaged deletion came back as a file")
if not (repo / "scratch.txt").is_file():
    bad.append("the untracked file is gone")
if git("stash", "list").stdout != "":
    bad.append("a stash entry was left behind")
if bad:
    print("the hook does not write a file staged in part back whole:")
    for line in bad:
        print(f"  {line}")
    print((commit.stdout + commit.stderr)[-1200:])
    print(git("status", "--porcelain").stdout)
    raise SystemExit(1)
print("PASS: the commit holds the staged hunk and the worktree came back whole, with no stash left")
PY
