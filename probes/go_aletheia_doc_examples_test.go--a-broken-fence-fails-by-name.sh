#!/usr/bin/env bash
# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
#
# Probes go/aletheia/doc_examples_test.go.
# Claim: the harness builds every Go fence with one build and runs each alone,
# in turn, and still names the fence that fails: a fence that does not compile
# fails the test with the build's error and the table mapping each built
# package to its file and line, and a fence that panics fails the subtest named
# by its file and line. Each case is staged in a Go fence appended to the Go
# README of a detached worktree of HEAD carrying the uncommitted diff, so the
# tree itself is never written.
# Non-zero exit: a broken fence passed, or failed without its file and line.
# Exits 2 without Go or the built library.
set -u
cd "$(dirname "$0")/.." || exit 2
lib=$PWD/build/libaletheia-ffi.so
[ -f "$lib" ] || exit 2
command -v go > /dev/null || exit 2
readme=go/README.md
[ -f "$readme" ] || exit 2

work=$(mktemp -d) || exit 2
tree=$work/tree
trap 'git worktree remove --force "$tree" > /dev/null 2>&1; rm -rf "$work"' EXIT
git worktree add -q --detach "$tree" HEAD || exit 2
git diff --no-ext-diff --no-color --binary --src-prefix=a/ --dst-prefix=b/ HEAD |
	git -C "$tree" apply --index --allow-empty || exit 2
cp "$tree/$readme" "$work/saved"
# The line of the fence about to be appended: the file's last line, plus the
# blank line before the fence.
line=$(($(wc -l < "$tree/$readme") + 2))
docs() { (cd "$tree/go" && ALETHEIA_LIB=$lib go test ./aletheia/ -run '^TestDocExamples$' -count=1); }

printf '\n```go\nvar broken int = "x"\n```\n' >> "$tree/$readme"
if docs > "$work/build.txt" 2>&1; then
	echo "a fence that does not compile passed"
	exit 1
fi
if ! grep -qF "the fences do not build" "$work/build.txt" || ! grep -qF " is $readme:L$line" "$work/build.txt"; then
	echo "a fence that does not compile failed without naming $readme:L$line:"
	head -8 "$work/build.txt" | sed 's/^/  /'
	exit 1
fi

cp "$work/saved" "$tree/$readme"
printf '\n```go\npanic("aletheia probe")\n```\n' >> "$tree/$readme"
if docs > "$work/run.txt" 2>&1; then
	echo "a fence that panics passed"
	exit 1
fi
if ! grep -qF -- "--- FAIL: TestDocExamples/$readme:L$line" "$work/run.txt"; then
	echo "a fence that panics failed without its own subtest $readme:L$line:"
	head -8 "$work/run.txt" | sed 's/^/  /'
	exit 1
fi
echo "PASS: a Go fence that does not compile, and one that panics, each fail the doc-example test by file and line"
