#!/usr/bin/env bash
# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
#
# Probes go/go.mod and go/excel/go.mod.
# Claim: both Go modules are named under the repository they live in, and under
# the directory inside it that holds them. A Go module path is not a label: it
# is where the toolchain goes to fetch the module, so a path naming somewhere
# else sends a consumer to whatever is served there. The remote is read from
# this checkout's own configuration and nothing is asked of the network.
# The path may carry a major-version suffix after the directory, which is how
# Go spells a major above the first, and that is checked elsewhere.
# Non-zero exit: a module is named somewhere other than where it is.
set -u
cd "$(dirname "$0")/.." || exit 2
url=$(git config --get remote.origin.url 2>/dev/null) || url=""
[ -n "$url" ] || { echo "this checkout has no origin remote, claim untestable"; exit 0; }

# git@host:owner/repo.git and https://host/owner/repo.git both name the same
# module prefix, which is host/owner/repo.
prefix=$(printf '%s\n' "$url" | sed -e 's|^git@|https://|' -e 's|^\(https://[^/:]*\):|\1/|' \
	-e 's|^https://||' -e 's|\.git$||' -e 's|/*$||')
[ -n "$prefix" ] || { echo "could not read a module prefix from the origin remote"; exit 2; }

status=0
for mod in go/go.mod go/excel/go.mod; do
	path=$(sed -n 's|^module \(.*\)$|\1|p' "$mod")
	[ -n "$path" ] || { echo "$mod declares no module path"; exit 2; }
	dir=$(dirname "$mod")
	want="$prefix/$dir"
	# The path is the repository prefix, the module's own directory, and at
	# most a major-version suffix after it.
	case "$path" in
		"$want") ;;
		"$want"/v[0-9] | "$want"/v[0-9][0-9]) ;;
		*) echo "$mod is named $path"
		   echo "  and it lives at $dir of $prefix, so its path is $want, optionally with a major-version suffix"
		   status=1 ;;
	esac
done
[ "$status" -eq 0 ] && echo "PASS: both modules are named under $prefix, at the directories that hold them"
exit $status
