#!/usr/bin/env bash
# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
#
# Probes go/go.work and the go.mod of every module it uses.
# Claim: every module and the workspace declare the same language version and
# the same toolchain, and each declares one.
#
# A workspace whose language version is below a module's makes that module build
# differently inside the workspace than outside it, which is where the tests run
# and where a consumer does not. Go reports some of those combinations and not
# others, and a language version raised in one module alone is the shape that
# goes unreported until a construct fails on a machine that builds the other.
# The modules are the ones the workspace lists, so a module it adds is held to
# this the day it is added.
# Non-zero exit: they do not agree, or one declares no toolchain. Exits 2
# without Go, or when the workspace lists no module.
set -u
cd "$(dirname "$0")/../go" || exit 2
command -v go > /dev/null || exit 2
[ -f go.work ] || exit 2
here=$(pwd -P)
modules=$(go list -m -f '{{.Dir}}') || exit 2
[ -n "$modules" ] || exit 2

directive() { grep -m1 "^$2 " "$1" | awk '{print $2}'; }

status=0
for what in go toolchain; do
	work=$(directive go.work "$what")
	if [ -z "$work" ]; then
		echo "the $what directive is missing from go.work"
		status=1
		continue
	fi
	for dir in $modules; do
		mod=${dir#"$here"/}
		[ "$dir" = "$here" ] && mod=.
		got=$(directive "$dir/go.mod" "$what")
		if [ -z "$got" ]; then
			echo "the $what directive is missing from $mod/go.mod"
			status=1
		elif [ "$got" != "$work" ]; then
			echo "the $what directive differs: $mod/go.mod $got, go.work $work"
			status=1
		fi
	done
done

[ "$status" -eq 0 ] || exit 1
echo "PASS: every module and the workspace declare $(directive go.work go) and $(directive go.work toolchain)"
