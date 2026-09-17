#!/usr/bin/env bash
# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
#
# Probes go/aletheia/issueseverity_string.go.
# Claim: the names the stringer output renders for IssueSeverity, taken from
# the line comments on the constants in go/aletheia/result.go, are the
# severities the wire carries, which go/aletheia/json.go reads by hand in a
# switch and which the kernel's validation issues use. Printing a severity and
# reading one back must agree even though nothing compiles the generated table
# against the parser. Non-zero exit: a name in the generated table is one the
# parser never accepts, the parser accepts a severity the table lacks, or the
# constant block carries no line-commented names.
set -u
cd "$(dirname "$0")/.." || exit 2
status=0

names=$(awk '/^\/\/go:generate stringer -type=IssueSeverity/{f=1} f && /^\)/{exit} f && /\/\/ [a-z_]+$/{sub(/.*\/\/ /, ""); print}' go/aletheia/result.go)
if [ -z "$names" ]; then
	echo "no line-commented IssueSeverity constants found"
	exit 1
fi

for n in $names; do
	grep -q "^const _IssueSeverity_name = \".*$n.*\"" go/aletheia/issueseverity_string.go ||
		{ echo "$n is not in the generated name table"; status=1; }
	grep -q "case \"$n\":" go/aletheia/json.go ||
		{ echo "the parser never reads the severity $n"; status=1; }
done

# The other direction: a severity the parser accepts and the enumeration lacks
# would decode to a constant that prints as a number.
accepted=$(awk '/severity := getString|switch s := getString\(issue, "severity"\)/{f=1} f && /^\t*}/{exit} f && /case "/{gsub(/.*case "|":.*/, ""); print}' go/aletheia/json.go)
for a in $accepted; do
	printf '%s\n' "$names" | grep -qx "$a" ||
		{ echo "the parser accepts $a, which the enumeration does not name"; status=1; }
done

if [ $status -eq 0 ]; then
	echo "PASS: the severities print and parse alike: $(printf '%s ' $names)"
fi
exit $status
