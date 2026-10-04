#!/usr/bin/env bash
# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
#
# Probes the test files of every module of the go/ workspace but the Excel
# loader: the binding and the benchmark harness in the core module, and the
# command-line interface, a module of its own. The Excel loader's suite reads
# workbooks through the kernel throughout and is left out by name, so a module
# the workspace adds is held to this unless it is named too.
# Claim: with cgo off every suite builds, runs the tests that need no kernel,
# and passes. The build without cgo is one the binding supports and its own
# verification list names, and a test that needs the kernel there used to die in
# a panic out of the re-exported formula printer, which is the kernel's. Those
# tests carry the build tag their code carries now, so the suite says nothing
# about them rather than failing. The command-line package answers the same way
# through its own guard, which asks whether the binding can load a library
# rather than only whether one was built: the tests that drive the real
# interface skip, and the rest run, the template tests among them, since the
# workbook is written without the kernel. The harness's tests drive its lane
# with an operation of their own and need no kernel at all.
#
# The count is asserted, not just the exit: a tag added to a file that did not
# need one would quietly shrink what runs, and that is the failure this is for.
# The number below is what the tree runs today; it moves with the suite, and a
# change to it is a change to how much the no-cgo build covers.
# Non-zero exit: a suite fails without cgo, or they run a different number of
# tests. Exits 2 without Go, or when the workspace lists no module.
set -u
cd "$(dirname "$0")/../go" || exit 2
command -v go > /dev/null || exit 2
expected=109
modules=$(go list -m -f '{{.Dir}}') || exit 2
[ -n "$modules" ] || exit 2
excel=$(go list -m -f '{{.Dir}}' github.com/Jaetan/aletheia/go/excel) || exit 2

work=$(mktemp -d) || exit 2
trap 'rm -rf "$work"' EXIT
: > "$work/out.txt"
for dir in $modules; do
	[ "$dir" = "$excel" ] && continue
	if ! (cd "$dir" && CGO_ENABLED=0 go test ./... -count=1 -v) > "$work/module.txt" 2>&1; then
		echo "a suite does not pass without cgo, in $dir:"
		grep -m3 -E "^--- FAIL|undefined:|panic:" "$work/module.txt" | sed 's/^/  /'
		exit 1
	fi
	cat "$work/module.txt" >> "$work/out.txt"
done
ran=$(grep -c "^--- PASS" "$work/out.txt")
if [ "$ran" -ne "$expected" ]; then
	echo "without cgo the suites run $ran tests, and this probe records $expected"
	echo "  a tag added or removed changes this; check which file moved and update the number"
	exit 1
fi
echo "PASS: without cgo every suite passes, running $ran tests of the ones that need no kernel"
