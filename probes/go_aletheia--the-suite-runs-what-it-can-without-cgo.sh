#!/usr/bin/env bash
# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
#
# Probes go/aletheia's test files.
# Claim: with cgo off the suite builds, runs the tests that need no kernel, and
# passes. The build without cgo is one the binding supports and its own
# verification list names, and a test that needs the kernel there used to die in
# a panic out of the re-exported formula printer, which is the kernel's. Those
# tests carry the build tag their code carries now, so the suite says nothing
# about them rather than failing.
#
# The count is asserted, not just the exit: a tag added to a file that did not
# need one would quietly shrink what runs, and that is the failure this is for.
# The number below is what the tree runs today; it moves with the suite, and a
# change to it is a change to how much the no-cgo build covers.
# Non-zero exit: the suite fails without cgo, or runs a different number of
# tests. Exits 2 without Go.
set -u
cd "$(dirname "$0")/../go" || exit 2
command -v go > /dev/null || exit 2
expected=76

work=$(mktemp -d) || exit 2
trap 'rm -rf "$work"' EXIT
if ! CGO_ENABLED=0 go test ./aletheia/ -count=1 -v > "$work/out.txt" 2>&1; then
	echo "the suite does not pass without cgo:"
	grep -m3 -E "^--- FAIL|undefined:|panic:" "$work/out.txt" | sed 's/^/  /'
	exit 1
fi
ran=$(grep -c "^--- PASS" "$work/out.txt")
if [ "$ran" -ne "$expected" ]; then
	echo "without cgo the suite runs $ran tests, and this probe records $expected"
	echo "  a tag added or removed changes this; check which file moved and update the number"
	exit 1
fi
echo "PASS: without cgo the suite passes, running $ran tests of the ones that need no kernel"
