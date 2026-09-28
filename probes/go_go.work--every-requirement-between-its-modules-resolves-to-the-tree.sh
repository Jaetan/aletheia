#!/usr/bin/env bash
# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
#
# Probes go/go.work against the go.mod of every module it uses.
# Claim: wherever one module of the workspace requires another, the version it
# names is one the required module's own path can carry, and the workspace
# replaces that module at that same version, so the requirement resolves to the
# tree instead of going to the network. Go refuses a major of 2 or more unless
# the module path ends in the matching /vN, so writing a release's tag without
# moving the path does not merely fail to fetch: the module stops parsing, and
# every command run inside it stops with it. The replace is version-specific,
# so a requirement changed without it silently stops resolving to the tree.
# The modules and their paths are the ones the workspace lists, read from their
# own files, never spelled here.
# Non-zero exit: a requirement names a version the path cannot carry, or no
# replace in the workspace names its version. Exits 2 without Go, or when the
# workspace lists no module or no module requires another.
set -u
cd "$(dirname "$0")/../go" || exit 2
command -v go > /dev/null || exit 2
here=$(pwd -P)
listing=$(go list -m -f '{{.Path}} {{.Dir}}') || exit 2
[ -n "$listing" ] || exit 2

status=0
pairs=0
while read -r _ dir; do
	mod=${dir#"$here"/}
	[ "$dir" = "$here" ] && mod=.
	while read -r required _; do
		version=$(grep -E "^[[:space:]]*(require[[:space:]]+)?$required[[:space:]]+v" "$dir/go.mod" |
			sed -n 's|.*[[:space:]]\(v[0-9][^[:space:]]*\).*$|\1|p' | head -1)
		[ -n "$version" ] || continue
		pairs=$((pairs + 1))

		major=${version#v}
		major=${major%%.*}
		if [ "$major" -ge 2 ]; then
			case "$required" in
				*"/v$major") ;;
				*) echo "$mod requires $required at $version, a path Go accepts only for v0 or v1:"
				   echo "  a major of $major needs the path to end in /v$major"
				   status=1 ;;
			esac
		fi

		if ! grep -qE "^replace[[:space:]]+$required[[:space:]]+$version[[:space:]]+=>" go.work; then
			echo "$mod requires $required at $version, and no replace in go.work names that version,"
			echo "  so the requirement does not resolve to the tree and Go goes to the network for it"
			status=1
		fi
	done <<< "$listing"
done <<< "$listing"

[ "$pairs" -gt 0 ] || { echo "no module of the workspace requires another"; exit 2; }
[ "$status" -eq 0 ] || exit 1
echo "PASS: $pairs requirements between the workspace's modules name carriable versions the workspace replaces"
