#!/usr/bin/env bash
# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
#
# Probes go/go.mod, go/excel/go.mod and go/go.work.
# Claim: the two modules and the workspace declare the same language version and
# the same toolchain, and both declare one.
#
# A workspace whose language version is below a module's makes that module build
# differently inside the workspace than outside it, which is where the tests run
# and where a consumer does not. Go reports some of those combinations and not
# others, and a language version raised in one module alone is the shape that
# goes unreported until a construct fails on a machine that builds the other.
# Non-zero exit: the three do not agree, or one declares no toolchain. Exits 2
# when a file is missing.
set -u
cd "$(dirname "$0")/../go" || exit 2
for f in go.mod excel/go.mod go.work; do
	[ -f "$f" ] || exit 2
done

directive() { grep -m1 "^$2 " "$1" | awk '{print $2}'; }

status=0
for what in go toolchain; do
	root=$(directive go.mod "$what")
	excel=$(directive excel/go.mod "$what")
	work=$(directive go.work "$what")
	if [ -z "$root" ] || [ -z "$excel" ] || [ -z "$work" ]; then
		echo "the $what directive is missing: go.mod '$root', excel/go.mod '$excel', go.work '$work'"
		status=1
		continue
	fi
	if [ "$root" != "$excel" ] || [ "$root" != "$work" ]; then
		echo "the $what directive differs: go.mod $root, excel/go.mod $excel, go.work $work"
		status=1
	fi
done

[ "$status" -eq 0 ] || exit 1
echo "PASS: both modules and the workspace declare $(directive go.mod go) and $(directive go.mod toolchain)"
