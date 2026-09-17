#!/usr/bin/env bash
# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
#
# Probes go/excel/go.mod against go/go.mod and go/go.work.
# Claim: the version the spreadsheet module requires the core module at is one
# the core module's own path can carry, and the workspace's replace names that
# same version, so the requirement resolves locally instead of going to the
# network. Go refuses a major of 2 or more unless the module path ends in the
# matching /vN, so writing the last release's tag here without moving the path
# does not merely fail to fetch: the module stops parsing, and every command
# run inside it stops with it. The replace is version-specific, so a
# requirement changed without it silently stops resolving to the tree.
# Non-zero exit: the requirement names a version the path cannot carry, the
# replace has drifted from it, or the module no longer builds offline.
set -u
cd "$(dirname "$0")/.." || exit 2
command -v go > /dev/null || { echo "go not installed, claim untestable"; exit 0; }
status=0

# The core module's path is read from its own file, never spelled here: a
# probe that spells a path is the thing that goes stale when the path moves.
core=$(sed -n 's|^module \(.*\)$|\1|p' go/go.mod)
[ -n "$core" ] || { echo "go/go.mod declares no module path"; exit 2; }
required=$(grep -F "$core " go/excel/go.mod | sed -n 's|.*[[:space:]]\(v[0-9][^ ]*\)$|\1|p' | head -1)
[ -n "$required" ] || { echo "go/excel/go.mod no longer requires $core"; exit 2; }

major=${required#v}
major=${major%%.*}
if [ "$major" -ge 2 ]; then
	case "$core" in
		*"/v$major") ;;
		*) echo "go/excel requires the core module at $required, and the core module's path is"
		   echo "  $core, which Go accepts only for v0 or v1: a major of $major needs the path to end in /v$major"
		   status=1 ;;
	esac
fi

replaced=$(grep -F "replace $core " go/go.work | sed -n 's|.*[[:space:]]\(v[0-9][^ ]*\)[[:space:]]*=>.*$|\1|p' | head -1)
if [ -n "$replaced" ] && [ "$replaced" != "$required" ]; then
	echo "the workspace replaces $replaced where the module requires $required, so the requirement"
	echo "  no longer resolves to the tree and Go goes to the network for it"
	status=1
fi

# The module parses and builds with what it requires, without the network.
out=$(cd go/excel && GOPROXY=off GOFLAGS=-mod=readonly go build ./... 2>&1)
rc=$?
if [ "$rc" -ne 0 ]; then
	echo "the spreadsheet module does not build offline under the workspace (exit $rc):"
	printf '%s\n' "$out" | head -4 | sed 's/^/    /'
	status=1
fi
[ "$status" -eq 0 ] && echo "PASS: the requirement is $required, which the path $core carries, and the workspace resolves it"
exit $status
