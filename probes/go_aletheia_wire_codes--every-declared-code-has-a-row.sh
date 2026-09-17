#!/usr/bin/env bash
# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
#
# Probes go/aletheia/error.go and go/aletheia/result.go against
# docs/WIRE_CODES.yaml.
# Claim: every wire code the binding declares has a row in the shared
# document, and every row has a constant. The suite's parity test compares the
# document against two lists written by hand in the test, so a constant added
# to the package and to neither the document nor those lists is invisible to
# it. This reads the constants out of the source instead, so the only way to
# pass is to add the row. Non-zero exit: a declared code has no row, or a row
# has no constant.
set -u
cd "$(dirname "$0")/.." || exit 2
yaml=docs/WIRE_CODES.yaml
for f in "$yaml" go/aletheia/error.go go/aletheia/result.go; do
	[ -f "$f" ] || { echo "missing $f"; exit 1; }
done

# The constants: Code* in error.go and Issue* in result.go, each declared with
# its wire string. IssueUnknown is the binding's own default for a code the
# wire did not carry, so it is not one of them.
declared=$(
	{
		grep -oP '^\tCode\w+\s*(=|string =)\s*"\K[a-z_]+' go/aletheia/error.go
		grep -oP '^\tIssue\w+\s+IssueCode = "\K[a-z_]+' go/aletheia/result.go
	} | grep -vx unknown | sort -u
)

# The document's rows, from both sections.
rows=$(grep -oP '^\s+- name:\s*\K[a-z_]+' "$yaml" | sort -u)

if [ -z "$declared" ] || [ -z "$rows" ]; then
	echo "one side yielded no code; the probe is reading it wrong"
	exit 1
fi

status=0
missing=$(comm -23 <(printf '%s\n' "$declared") <(printf '%s\n' "$rows"))
stale=$(comm -13 <(printf '%s\n' "$declared") <(printf '%s\n' "$rows"))
if [ -n "$missing" ]; then
	echo "declared by the binding with no row in the document:"
	printf '%s\n' "$missing" | sed 's/^/  /'
	status=1
fi
if [ -n "$stale" ]; then
	echo "a row in the document with no constant in the binding:"
	printf '%s\n' "$stale" | sed 's/^/  /'
	status=1
fi
if [ $status -eq 0 ]; then
	echo "PASS: $(printf '%s\n' "$declared" | wc -l) codes, each declared and each with a row"
fi
exit $status
