#!/usr/bin/env bash
# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
#
# Probes go/go.work.
# Claim: the Excel module builds against the core module in the tree, with the
# network refused. That is what the workspace's replace buys: the module
# requires the core at a placeholder version no tag carries, and the use
# directive alone does not resolve it, since it registers the module and leaves
# the version to the require. Without the replace, a build reaches for the
# network and a machine without one cannot build the module at all.
# Non-zero exit: the module needs the network to build from this tree. Exits 2
# without Go.
set -u
cd "$(dirname "$0")/../go" || exit 2
command -v go > /dev/null || exit 2

work=$(mktemp -d) || exit 2
trap 'rm -rf "$work"' EXIT

if ! (cd excel && GOPROXY=off GOFLAGS=-mod=readonly go build ./...) > "$work/build.txt" 2>&1; then
	echo "the excel module does not build from the workspace without the network:"
	head -3 "$work/build.txt" | sed 's/^/  /'
	exit 1
fi
echo "PASS: the excel module builds against the core module in the tree, with no network"
