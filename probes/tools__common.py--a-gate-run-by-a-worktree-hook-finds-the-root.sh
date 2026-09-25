#!/usr/bin/env bash
# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
#
# Probes tools/_common.py, git_toplevel.
# Claim: a gate run by a git hook in a linked worktree finds the worktree's
# root. Git exports GIT_DIR to a hook there, and a lookup anchored on the
# tools directory then answers the tools directory itself, so the SPDX gate
# looked for LICENSE.md inside it. The probe commits in a detached worktree of
# HEAD carrying the uncommitted diff, with a hooks directory whose pre-commit
# runs the SPDX gate and refuses the commit, so no commit is made.
# Non-zero exit: 1 when the gate fails under the hook, 3 when git no longer
# exports GIT_DIR to the hook (the probe no longer reaches the defect), 2 when
# git or the interpreter is missing or the worktree cannot be made.
set -u
cd "$(dirname "$0")/.." || exit 2
repo=$PWD
py=$repo/python/.venv/bin/python
command -v git > /dev/null && [ -x "$py" ] || exit 2
scratch=$repo/cpp/build/probe-scratch/toplevel-worktree-hook
git worktree remove --force "$scratch/wt" 2> /dev/null
rm -rf "$scratch"
mkdir -p "$scratch/hooks" || exit 2
trap 'git worktree remove --force "$scratch/wt" 2> /dev/null; rm -rf "$scratch"' EXIT
git worktree add -q --detach "$scratch/wt" HEAD || exit 2
if ! git diff --quiet HEAD; then
    git diff --binary HEAD | git -C "$scratch/wt" apply --whitespace=nowarn || exit 2
fi

cat > "$scratch/hooks/pre-commit" <<HOOK
#!/usr/bin/env bash
printf '%s\n' "\${GIT_DIR-unset}" > "$scratch/git-dir"
"$py" -m tools.check_spdx_headers > "$scratch/gate.log" 2>&1
echo \$? > "$scratch/gate.rc"
exit 1
HOOK
chmod +x "$scratch/hooks/pre-commit"

git -C "$scratch/wt" -c core.hooksPath="$scratch/hooks" -c commit.gpgsign=false \
    -c user.name=probe -c user.email=probe@invalid \
    commit -q --allow-empty -m probe > /dev/null 2>&1
[ -f "$scratch/gate.rc" ] || { echo "the hook did not run"; exit 2; }
[ "$(cat "$scratch/git-dir")" != unset ] || { echo "git no longer exports GIT_DIR to a worktree hook"; exit 3; }
rc=$(cat "$scratch/gate.rc")
[ "$rc" -eq 0 ] || { echo "the SPDX gate exited $rc under a worktree hook:"; cat "$scratch/gate.log"; exit 1; }
