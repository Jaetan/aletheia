#!/usr/bin/env bash
# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
#
# Probes go/go.work.sum and the go.sum of every module go/go.work uses.
# Claim: every module a checksum file names is one the workspace's module graph
# still names, and every hash the build reads is the one the module carries.
#
# The second half is what a build already enforces, and it is checked here by
# building, since `go mod verify` does not read these files at all: it compares
# the module cache against itself and passes over a checksum this file has
# wrong. The first half nothing enforces. An entry left behind by a dependency
# that has gone fails nothing, the file grows, and the next reader cannot tell
# which lines are load bearing. The orchestrator's Go steps are the formatter
# and the vetter, and neither looks. The modules are the ones the workspace
# lists, so a module it adds is held to this the day it is added.
# Non-zero exit: a checksum names a module the graph does not, or a module does
# not match the hash recorded for it. Exits 2 without Go.
set -u
cd "$(dirname "$0")/../go" || exit 2
command -v go > /dev/null || exit 2

work=$(mktemp -d) || exit 2
trap 'rm -rf "$work"' EXIT

here=$(pwd -P)
modules=$(go list -m -f '{{.Dir}}') || exit 2
[ -n "$modules" ] || exit 2

if ! go list -m all > "$work/graph.txt" 2> "$work/graph.err"; then
	echo "the module graph could not be listed:"
	head -3 "$work/graph.err" | sed 's/^/  /'
	exit 2
fi
cut -d' ' -f1 "$work/graph.txt" | sort -u > "$work/graph.names"

status=0
for sum in $(for dir in $modules; do printf '%s/go.sum\n' "$dir"; done) go.work.sum; do
	[ -f "$sum" ] || continue
	cut -d' ' -f1 "$sum" | sort -u > "$work/sum.names"
	stale=$(comm -23 "$work/sum.names" "$work/graph.names")
	if [ -n "$stale" ]; then
		echo "${sum#"$here"/} names modules the workspace no longer uses:"
		printf '%s\n' "$stale" | sed 's/^/  /'
		status=1
	fi
done

# Building reads every hash the compilation needs, and refuses a module whose
# archive does not match the one recorded here.
# Every module, since one directory's ellipsis stops at that module's edge and
# the dependencies these checksums are mostly about belong to another.
for dir in $modules; do
	# -o /dev/null: a module holding one main package would otherwise write
	# its executable into the tree.
	if ! (cd "$dir" && go build -o /dev/null ./...) > "$work/build.txt" 2>&1; then
		echo "the ${dir#"$here"/} module does not build against these checksums:"
		head -3 "$work/build.txt" | sed 's/^/  /'
		status=1
	fi
done

[ "$status" -eq 0 ] || exit 1
echo "PASS: every checksum names a module the workspace uses, and every module matches it"
