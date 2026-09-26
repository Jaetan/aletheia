#!/usr/bin/env bash
# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
#
# Probes tools/check_no_review_marks.py.
# Claim: a tracked file the gate cannot read is reported, by path, with exit 2,
# not passed over as clean. The index still lists a file deleted from the
# worktree, so the walk reaches it and the read fails whatever the caller's
# permissions are. The check runs against a throwaway repository under the
# build tree, so the worktree is never modified. Non-zero exit: 1 when a clean
# tree is refused, when the unreadable file is passed over, or when the report
# does not name it; 2 when git or the interpreter is missing.
set -u
cd "$(dirname "$0")/.." || exit 2
repo=$PWD
py=$repo/python/.venv/bin/python
command -v git > /dev/null && [ -x "$py" ] || exit 2
scratch=cpp/build/probe-scratch/check_no_review_marks-unreadable
rm -rf "$scratch"
mkdir -p "$scratch" || exit 2
trap 'rm -rf "$scratch"' EXIT
# The gate anchors its repository root on its own module path, so the copy of
# the package is what puts the throwaway repository in scope. Only the fixture
# is tracked: the copy stays untracked, and the walk never reads it.
cp -r tools "$scratch/tools" || exit 2
printf 'a plain line\n' > "$scratch/note.txt"
(cd "$scratch" && git init -q . && git add -- note.txt) || exit 2

run() { (cd "$scratch" && "$py" -m tools.check_no_review_marks 2>&1); }

out=$(run); rc=$?
[ "$rc" -eq 0 ] || { echo "a clean tree was refused (exit $rc): $out"; exit 1; }

rm -f "$scratch/note.txt"
out=$(run); rc=$?
[ "$rc" -eq 2 ] || { echo "a tracked file that cannot be read exited $rc, not 2: $out"; exit 1; }
case $out in *note.txt*) ;; *) echo "the report does not name the unreadable file: $out"; exit 1 ;; esac
