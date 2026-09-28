#!/usr/bin/env bash
# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
#
# Probes tools/_ci_steps.py, its cgo-free build of every Go module.
# Claim: the build compiles every package of every module the workspace lists
# and leaves the tree as it found it. `go build ./...` over a module holding a
# single main package writes that executable into the module's directory, and
# the command line is such a module: a plain build left a ten-megabyte binary
# in the tree on every sweep.
# The step's own command is read from the module and run only once it has the
# one shape this probe expects, never as whatever the file happens to hold.
# Non-zero exit: the build fails, or the tree differs after it. Exits 2
# without Go or the venv, when the command cannot be read or has another
# shape, or when the tree is already dirty under go/ in a way the run would
# mask.
set -u
cd "$(dirname "$0")/.." || exit 2
command -v go > /dev/null || exit 2
py=python/.venv/bin/python
[ -x "$py" ] || exit 2
cmd=$("$py" -c 'from tools._ci_steps import GO_BUILD_NO_CGO, in_every_go_module
print(GO_BUILD_NO_CGO)
print(in_every_go_module(GO_BUILD_NO_CGO))') || exit 2
build=$(printf '%s\n' "$cmd" | sed -n 1p)
loop=$(printf '%s\n' "$cmd" | sed -n 2p)
case $build in
	"CGO_ENABLED=0 go build ./..." | "CGO_ENABLED=0 go build -o /dev/null ./...") ;;
	*) echo "the step builds with a command of another shape: $build"; exit 2 ;;
esac
case $loop in
	"mods=\$(go list -m -f '{{.Dir}}') && test -n \"\$mods\" || exit 1; for m in \$mods; do (cd \"\$m\" && $build) || exit 1; done") ;;
	*) echo "the step runs the build through a loop of another shape: $loop"; exit 2 ;;
esac

work=$(mktemp -d) || exit 2
trap 'rm -rf "$work"' EXIT
git status --porcelain --untracked-files=all -- go > "$work/before.txt" || exit 2
(cd go && sh -c "$loop") > "$work/build.txt" 2>&1
rc=$?
git status --porcelain --untracked-files=all -- go > "$work/after.txt" || exit 2
if [ "$rc" -ne 0 ]; then
	echo "the build failed (exit $rc):"
	tail -5 "$work/build.txt" | sed 's/^/  /'
	exit 1
fi
if ! diff -u "$work/before.txt" "$work/after.txt" > "$work/diff.txt"; then
	echo "the build left the tree changed under go/:"
	sed -n '3,$p' "$work/diff.txt" | grep '^+' | sed 's/^+/  /'
	# What the build wrote is removed again: only a path untracked after the
	# run and absent from the listing before it.
	sed -n '3,$p' "$work/diff.txt" | sed -n 's/^+?? //p' | while IFS= read -r path; do
		rm -f -- "$path"
	done
	exit 1
fi
echo "PASS: the cgo-free build of every module leaves the tree as it found it"
