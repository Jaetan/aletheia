#!/usr/bin/env bash
# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
#
# Probes go/aletheia/fuzz_test.go.
# Claim: the fuzz targets the file declares are exactly the ones the Go
# binding's own standard names, no more and no fewer. The standard lists them
# in prose, so nothing compiles the two lists against each other: a target
# renamed here, or one added to the standard and never written, is invisible
# until someone reads both. Non-zero exit: the two lists differ, or either
# file stopped carrying its list.
set -u
cd "$(dirname "$0")/.." || exit 2
target_file=go/aletheia/fuzz_test.go
standard=AGENTS/go.md
for f in "$target_file" "$standard"; do
	[ -f "$f" ] || { echo "missing $f"; exit 1; }
done

declared=$(grep -oP '^func \KFuzz\w+' "$target_file" | sort -u)
# The standard names them as inline code on the line that introduces the
# native fuzz tests.
named=$(grep -oP '`\KFuzz\w+(?=`)' "$standard" | sort -u)

if [ -z "$declared" ]; then
	echo "no fuzz target declared in $target_file"
	exit 1
fi
if [ -z "$named" ]; then
	echo "no fuzz target named in $standard"
	exit 1
fi

only_declared=$(comm -23 <(printf '%s\n' "$declared") <(printf '%s\n' "$named"))
only_named=$(comm -13 <(printf '%s\n' "$declared") <(printf '%s\n' "$named"))
if [ -z "$only_declared" ] && [ -z "$only_named" ]; then
	echo "PASS: the same $(printf '%s\n' "$declared" | wc -l) targets are declared and named"
	exit 0
fi
if [ -n "$only_declared" ]; then
	echo "declared but not named by the standard:"
	printf '%s\n' "$only_declared" | sed 's/^/  /'
fi
if [ -n "$only_named" ]; then
	echo "named by the standard but not declared:"
	printf '%s\n' "$only_named" | sed 's/^/  /'
fi
exit 1
