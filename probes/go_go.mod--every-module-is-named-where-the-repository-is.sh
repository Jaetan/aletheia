#!/usr/bin/env bash
# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
#
# Probes the go.mod of every module go/go.work uses.
# Claim: every Go module is named under the repository it lives in, and under
# the directory inside it that holds it. A Go module path is not a label: it
# is where the toolchain goes to fetch the module, so a path naming somewhere
# else sends a consumer to whatever is served there. The remote is read from
# this checkout's own configuration and nothing is asked of the network. The
# modules are the ones the workspace lists, so a module it adds is held to this
# the day it is added.
# The path may carry a major-version suffix after the directory, which is how
# Go spells a major above the first, and that is checked elsewhere.
# Non-zero exit: a module is named somewhere other than where it is. Exits 2
# without Go, or when the workspace lists no module.
set -u
cd "$(dirname "$0")/.." || exit 2
command -v go > /dev/null || exit 2
url=$(git config --get remote.origin.url 2>/dev/null) || url=""
[ -n "$url" ] || { echo "this checkout has no origin remote, claim untestable"; exit 0; }

# git@host:owner/repo.git and https://host/owner/repo.git both name the same
# module prefix, which is host/owner/repo.
prefix=$(printf '%s\n' "$url" | sed -e 's|^git@|https://|' -e 's|^\(https://[^/:]*\):|\1/|' \
	-e 's|^https://||' -e 's|\.git$||' -e 's|/*$||')
[ -n "$prefix" ] || { echo "could not read a module prefix from the origin remote"; exit 2; }

root=$(pwd -P)
listing=$(cd go && go list -m -f '{{.Path}} {{.Dir}}') || exit 2
[ -n "$listing" ] || exit 2

status=0
while read -r path moddir; do
	dir=${moddir#"$root"/}
	want="$prefix/$dir"
	# The path is the repository prefix, the module's own directory, and at
	# most a major-version suffix after it.
	case "$path" in
		"$want") ;;
		"$want"/v[0-9] | "$want"/v[0-9][0-9]) ;;
		*) echo "$dir/go.mod is named $path"
		   echo "  and it lives at $dir of $prefix, so its path is $want, optionally with a major-version suffix"
		   status=1 ;;
	esac
done <<< "$listing"
[ "$status" -eq 0 ] && echo "PASS: every module is named under $prefix, at the directory that holds it"
exit $status
