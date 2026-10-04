#!/usr/bin/env bash
# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
#
# Probes tools/sweep_evidence.py.
# Claim: worktree_tree names the rewritten content of a file whose stat data
# git cannot tell from the indexed file's: written, indexed and rewritten at
# its size at one instant, the index stamped with that instant too. The probe
# first shows the case is real, a copy of the index stamped now letting
# `git add --update` keep the old content, then asks worktree_tree. Every
# timestamp is set, and core.trustctime is off since no call sets a change
# time, so no clock decides the outcome. The repository is a throwaway one
# under the build tree. Non-zero exit: 1 when the fresh-stamped copy sees the
# rewrite (the probe no longer builds the case) or when worktree_tree names a
# tree without it; 2 when git, touch or the interpreter is missing.
set -u
cd "$(dirname "$0")/.." || exit 2
repo=$PWD
py=$repo/python/.venv/bin/python
command -v git > /dev/null && command -v touch > /dev/null && [ -x "$py" ] || exit 2
scratch=$repo/cpp/build/probe-scratch/sweep_evidence-racy-rewrite
rm -rf "$scratch"
mkdir -p "$scratch/repo" || exit 2
trap 'rm -rf "$scratch"' EXIT
at=@1000000000
g() { git -C "$scratch/repo" "$@"; }

g init -q && g config core.trustctime false || exit 2
printf 'one\n' > "$scratch/repo/a.txt" && touch -d "$at" "$scratch/repo/a.txt" || exit 2
g add a.txt &&
	g -c user.email=probe@example.com -c user.name=probe -c commit.gpgsign=false commit -q -m base || exit 2
touch -d "$at" "$scratch/repo/.git/index" || exit 2
printf 'two\n' > "$scratch/repo/a.txt" && touch -d "$at" "$scratch/repo/a.txt" || exit 2

cp "$scratch/repo/.git/index" "$scratch/fresh-index" || exit 2
GIT_INDEX_FILE=$scratch/fresh-index g add --update || exit 2
fresh=$(GIT_INDEX_FILE=$scratch/fresh-index g write-tree) || exit 2
seen=$(g show "$fresh:a.txt") || exit 2
[ "$seen" = one ] || { echo "a copy stamped now saw the rewrite ($seen): the case is not built"; exit 1; }

tree=$(
	"$py" -c 'import sys; from pathlib import Path; from tools.sweep_evidence import worktree_tree; print(worktree_tree(Path(sys.argv[1])))' \
		"$scratch/repo"
) || exit 2
seen=$(g show "$tree:a.txt" 2>&1)
[ "$seen" = two ] || { echo "worktree_tree named $tree, whose a.txt reads: $seen"; exit 1; }
