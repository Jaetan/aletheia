#!/usr/bin/env bash
# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
#
# Probes go/aletheia/verdict_string.go.
# Claim: the names the stringer output renders for Verdict, taken from
# the line comments on the constants in go/aletheia/result.go, are the
# verdicts the wire carries, which go/aletheia/json.go reads by hand in a
# switch over the status of a verdict. Printing a verdict and
# reading one back must agree even though nothing compiles the generated table
# against the parser. Non-zero exit: a name in the generated table is one the
# parser never accepts, the parser accepts a verdict the table lacks, or the
# constant block carries no line-commented names.
set -u
cd "$(dirname "$0")/.." || exit 2
status=0

names=$(awk '/^\/\/go:generate stringer -type=Verdict/{f=1} f && /^\)/{exit} f && /\/\/ [a-z_]+$/{sub(/.*\/\/ /, ""); print}' go/aletheia/result.go)
if [ -z "$names" ]; then
	echo "no line-commented Verdict constants found"
	exit 1
fi

for n in $names; do
	grep -q "^const _Verdict_name = \".*$n.*\"" go/aletheia/verdict_string.go ||
		{ echo "$n is not in the generated name table"; status=1; }
	grep -q "case \"$n\":" go/aletheia/json.go ||
		{ echo "the parser never reads the verdict $n"; status=1; }
done

# The other direction: a verdict the parser accepts and the enumeration lacks
# would decode to a constant that prints as a number.
accepted=$(awk '/switch entryStatus \{/{f=1} f && /^\t*}/{exit} f && /case "/{gsub(/.*case "|":.*/, ""); print}' go/aletheia/json.go)
for a in $accepted; do
	printf '%s\n' "$names" | grep -qx "$a" ||
		{ echo "the parser accepts $a, which the enumeration does not name"; status=1; }
done

if [ $status -eq 0 ]; then
	echo "PASS: the verdicts print and parse alike: $(printf '%s ' $names)"
fi
exit $status
