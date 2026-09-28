#!/usr/bin/env bash
# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
#
# Probes go/go.work.
# Claim: every module the workspace uses builds against the other modules in
# the tree, with the network refused. That is what the workspace's replaces
# buy: a module requires another at a placeholder version no tag carries, and
# the use directive alone does not resolve it, since it registers the module
# and leaves the version to the require. Without the replace, a build reaches
# for the network and a machine without one cannot build the module at all.
# The modules are the ones the workspace lists, so a module it adds is held to
# this the day it is added.
# Non-zero exit: a module needs the network to build from this tree. Exits 2
# without Go, or when the workspace lists no module.
set -u
cd "$(dirname "$0")/../go" || exit 2
command -v go > /dev/null || exit 2
here=$(pwd -P)
modules=$(go list -m -f '{{.Dir}}') || exit 2
[ -n "$modules" ] || exit 2

work=$(mktemp -d) || exit 2
trap 'rm -rf "$work"' EXIT

status=0
for dir in $modules; do
	mod=${dir#"$here"/}
	[ "$dir" = "$here" ] && mod=.
	# -o /dev/null: a module holding one main package would otherwise write
	# its executable into the tree.
	if ! (cd "$dir" && GOPROXY=off GOFLAGS=-mod=readonly go build -o /dev/null ./...) > "$work/build.txt" 2>&1; then
		echo "the $mod module does not build from the workspace without the network:"
		head -3 "$work/build.txt" | sed 's/^/  /'
		status=1
	fi
done
[ "$status" -eq 0 ] || exit 1
echo "PASS: every module builds against the others in the tree, with no network"
