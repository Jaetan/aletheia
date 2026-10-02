#!/usr/bin/env bash
# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
#
# Probes go/aletheia/json.go, the declaration of narrow.
# Claim: the not-covered mutants the Go baseline records on narrow's
# declaration are mutants no build can carry. gremlins reads each | of the
# constraint's type set as a bitwise or and would invert it to &, which Go's
# grammar does not admit there, so every such mutant fails to parse. Each | is
# inverted alone in a scratch copy of the declaration and gofmt must refuse
# every one, while it parses the declaration as written.
# Non-zero exit: the declaration is not found, its constraint carries no |, the
# harness refuses the declaration as written, or an inversion parses.
set -u
cd "$(dirname "$0")/.." || exit 2
command -v gofmt > /dev/null || { echo "gofmt not installed, claim untestable"; exit 0; }
work=$(mktemp -d) || exit 2
trap 'rm -rf "$work"' EXIT

line=$(grep -m1 '^func narrow\[' go/aletheia/json.go) || {
	echo "no narrow declaration in go/aletheia/json.go"
	exit 1
}
parses() {
	printf 'package p\n\n%s\n\treturn 0, false\n}\n' "$1" > "$work/m.go"
	gofmt -e "$work/m.go" > /dev/null 2>&1
}
parses "$line" || { echo "the harness refuses the declaration as written: $line"; exit 1; }
n=$(printf '%s' "$line" | tr -cd '|' | wc -c)
[ "$n" -gt 0 ] || { echo "the constraint carries no |: $line"; exit 1; }
for i in $(seq 1 "$n"); do
	mutated=$(printf '%s\n' "$line" | awk -v k="$i" '{
		c = 0; out = ""
		for (j = 1; j <= length($0); j++) {
			ch = substr($0, j, 1)
			if (ch == "|" && ++c == k) ch = "&"
			out = out ch
		}
		print out
	}')
	if parses "$mutated"; then
		echo "inverting | $i of $n parses: $mutated"
		exit 1
	fi
done
echo "PASS: none of the $n inversions of narrow's type set parses"
