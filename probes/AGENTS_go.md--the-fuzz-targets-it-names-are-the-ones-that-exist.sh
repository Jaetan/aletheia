#!/usr/bin/env bash
# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
#
# Probes AGENTS/go.md.
# Claim: the fuzz targets the standard names are the ones the binding has, and
# the lane it describes is the one that runs. It described a lane that fuzzed
# each target for a minute on every change and an hour nightly, and neither
# existed: no workflow and no tool in the tree invokes a fuzz run, which is what
# made the sentence worth checking rather than believing.
# Non-zero exit: the standard names a target the binding does not have, the
# binding has one the standard does not name, or something starts fuzzing on a
# schedule while the standard says nothing does. Exits 2 when a file has moved.
set -u
cd "$(dirname "$0")/.." || exit 2
doc=AGENTS/go.md
targets=go/aletheia/fuzz_test.go
[ -f "$doc" ] && [ -f "$targets" ] || exit 2

in_doc=$(grep -oE "\`Fuzz[A-Za-z]+\`" "$doc" | tr -d '`' | sort -u)
in_code=$(grep -oE "^func Fuzz[A-Za-z]+" "$targets" | sed 's/func //' | sort -u)
status=0
if [ "$in_doc" != "$in_code" ]; then
	echo "the standard and the binding name different targets:"
	diff <(printf '%s\n' "$in_doc") <(printf '%s\n' "$in_code") | sed 's/^/  /'
	status=1
fi

# Nothing schedules a fuzz run, which is what the standard now says.
scheduled=$(grep -rln "fuzztime\|-fuzz=" .github/workflows/ tools/ 2>/dev/null || true)
if [ -n "$scheduled" ]; then
	echo "something runs a fuzz lane, and the standard says fuzzing is a command someone types:"
	printf '%s\n' "$scheduled" | sed 's/^/  /'
	status=1
fi

[ "$status" -eq 0 ] || exit 1
echo "PASS: the standard names the $(printf '%s\n' "$in_code" | wc -l) targets the binding has, and nothing fuzzes on a schedule"
