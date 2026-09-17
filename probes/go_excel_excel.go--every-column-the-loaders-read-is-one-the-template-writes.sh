#!/usr/bin/env bash
# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
#
# Probes go/excel/excel.go.
# Claim: every column name the loaders look a value up under is a header the
# template writes. The two are separate lists of strings, one written into the
# workbook and one read back out of it, so a header renamed on one side and not
# the other produces a template whose own rows the loader refuses as missing a
# field. The tests fill workbooks from the header lists, so they cannot see it.
# Non-zero exit: a loader reads a column no template sheet carries. Exits 2 when
# the source is not where this expects it.
set -u
cd "$(dirname "$0")/.." || exit 2
src=go/excel/excel.go
[ -f "$src" ] || exit 2

# The three header lists, as written in the var block.
headers=$(sed -n '/^var (/,/^)$/p' "$src" | grep -oE '"[^"]+"' | tr -d '"' | sort -u)
[ -n "$headers" ] || { echo "no header was read from $src"; exit 1; }

# Every column a value is looked up under: the four cell readers, the direct
# map lookups, and the columns a condition is told to require.
reads=$(
	grep -oE 'xlsx(Str|Rational|Int|Bool)\((row|d), "[^"]+"' "$src" | grep -oE '"[^"]+"'
	grep -oE '\b(row|d)\["[^"]+"\]' "$src" | grep -oE '"[^"]+"'
	grep -oE 'requireColumns\([^)]*\)' "$src" | grep -oE '"[^"]+"'
)
reads=$(printf '%s\n' "$reads" | tr -d '"' | sort -u)
[ -n "$reads" ] || { echo "no column read was found in $src"; exit 1; }

# The words requireColumns takes that name the kind of condition, not a column.
missing=$(comm -23 <(printf '%s\n' "$reads") <(printf '%s\n' "$headers") |
	grep -vxE 'condition|then condition')
if [ -n "$missing" ]; then
	echo "read by a loader and written by no template sheet:"
	printf '%s\n' "$missing" | sed 's/^/  /'
	exit 1
fi
echo "PASS: every column the loaders read is a header the template writes"
