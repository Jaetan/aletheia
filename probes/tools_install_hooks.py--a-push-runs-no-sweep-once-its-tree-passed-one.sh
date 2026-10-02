#!/usr/bin/env bash
# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
#
# Probes tools/install_hooks.py, the pre-push hook body it installs, with
# tools/sweep_evidence.py as it stands.
# Claim: git connects before it runs the pre-push hook, so a push whose tree
# already passed a full sweep must run none; a push whose tree has no passing
# sweep on record, and whose sweep records none, must not land. The unit tests
# hand the hook ref lines they wrote; this probe pushes for real, to a bare
# repository beside a scratch one, so the ref lines are git's own. The scratch
# repository carries the tree's evidence module and the two tools modules it
# imports, a sweep stub that passes and writes down that it ran, and one
# finished log that vouches for the first commit's tree. The first push must
# land with no sweep; a second commit, which no log vouches for, must be
# refused after the sweep runs, leaving the remote where the first push put
# it. The caller's global git configuration is shut out, so a signing
# setting there cannot stop a commit on a passphrase. An optional first
# argument names the hook source to render from, in place of the tree's own.
# Non-zero exit: 1 when a push swept where it had a record, landed without
# one, or was refused with one; 2 when the scratch repositories could not be
# made or the toolchain is missing.
set -u
cd "$(dirname "$0")/.." || exit 2
py=$PWD/python/.venv/bin/python
[ -x "$py" ] || exit 2
src=${1:-tools/install_hooks.py}
[ -f "$src" ] || exit 2
work=$(mktemp -d) || exit 2
trap 'rm -rf "$work"' EXIT

"$py" - "$src" "$work" "$PWD" <<'PY'
import importlib.util
import os
import shutil
import stat
import subprocess
import sys
from pathlib import Path

src, work, root = Path(sys.argv[1]), Path(sys.argv[2]), Path(sys.argv[3])
spec = importlib.util.spec_from_file_location("install_hooks_under_probe", src)
module = importlib.util.module_from_spec(spec)
spec.loader.exec_module(module)
body = module.PRE_PUSH_BODY.split("\n", 1)[1]

env = {**os.environ, "GIT_CONFIG_GLOBAL": os.devnull, "GIT_CONFIG_NOSYSTEM": "1"}
repo, remote = work / "repo", work / "remote.git"


def git(*args, cwd=repo, check=True):
    return subprocess.run(
        ["git", *args], cwd=cwd, env=env, capture_output=True, text=True, check=check
    )


try:
    remote.mkdir()
    git("init", "-q", "--bare", cwd=remote)
    repo.mkdir()
    git("init", "-q")
    git("config", "user.name", "hook probe")
    git("config", "user.email", "hook@probe")
    git("remote", "add", "origin", str(remote))
    tools = repo / "tools"
    tools.mkdir()
    for name in ("__init__.py", "_common.py", "check_gate_claim.py", "sweep_evidence.py"):
        shutil.copyfile(root / "tools" / name, tools / name)
    (tools / "run_ci.py").write_text(
        "import pathlib\npathlib.Path('swept').write_text('yes')\n", encoding="utf-8"
    )
    (repo / ".gitignore").write_text("tools/ci-output/\nswept\n", encoding="utf-8")
    (repo / "notes.txt").write_text("one\n", encoding="utf-8")
    git("add", ".")
    git("commit", "-q", "-m", "base")
    tree = git("rev-parse", "HEAD^{tree}").stdout.strip()
    sys.path.insert(0, str(repo))
    from tools.sweep_evidence import TREE_LINE

    logs = tools / "ci-output"
    logs.mkdir()
    (logs / "ci-probe.log").write_text(
        "\n".join(
            [
                "═══ Aletheia offline CI sweep ═══",
                f"{TREE_LINE}{tree}",
                "─── a step ───",
                "═══ CI summary ═══",
                "Result:   ALL 1 STEPS PASSED",
                f"{TREE_LINE}{tree}",
                "",
            ]
        ),
        encoding="utf-8",
    )
except (subprocess.CalledProcessError, OSError, ImportError) as exc:
    print(f"the scratch repositories could not be made: {exc}")
    raise SystemExit(2)

hook = repo / ".git" / "hooks" / "pre-push"
hook.write_text("#!" + sys.executable + "\n" + body, encoding="utf-8")
hook.chmod(hook.stat().st_mode | stat.S_IXUSR)
swept = repo / "swept"
bad = []

first = git("push", "-q", "origin", "HEAD:refs/heads/main", check=False)
base = git("rev-parse", "HEAD").stdout.strip()
landed = git("rev-parse", "--verify", "--quiet", "refs/heads/main", cwd=remote, check=False)
if first.returncode != 0:
    bad.append(f"the push whose tree passed a sweep was refused (exit {first.returncode})")
elif landed.stdout.strip() != base:
    bad.append("the push whose tree passed a sweep did not land")
if swept.exists():
    bad.append("the push whose tree passed a sweep ran the sweep again")
    swept.unlink()

(repo / "notes.txt").write_text("two\n", encoding="utf-8")
git("commit", "-q", "-am", "unswept")
second = git("push", "-q", "origin", "HEAD:refs/heads/main", check=False)
after = git("rev-parse", "--verify", "--quiet", "refs/heads/main", cwd=remote, check=False)
if not swept.exists():
    bad.append("the push whose tree had no record did not run the sweep")
if second.returncode == 0:
    bad.append("the push whose sweep recorded no tree was allowed")
if after.stdout.strip() != base:
    bad.append("the remote moved on a push whose tree no sweep vouched for")

if bad:
    print("the pre-push hook does not hold a push to a sweep of its own tree:")
    for line in bad:
        print(f"  {line}")
    print((first.stderr + second.stderr)[-1500:])
    raise SystemExit(1)
print("PASS: a push with a record ran no sweep and landed; one without was swept and refused")
PY
