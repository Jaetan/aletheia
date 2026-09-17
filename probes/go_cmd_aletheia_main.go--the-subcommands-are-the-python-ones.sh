#!/usr/bin/env bash
# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
#
# Probes go/cmd/aletheia/main.go.
# Claim: the Go interface answers every subcommand `python -m aletheia` answers.
# Its own header says so, and the one it does not carry out, check, it refuses by
# name rather than reporting an unknown command, which is what tells a user that
# the surface is shared and this one thing is missing.
# The lists are read from the two sources: the Go dispatch and the Python
# subparsers.
# Non-zero exit: one interface carries a subcommand the other does not, or the
# missing one is not refused by name. Exits 2 without Go or without a built
# kernel.
set -u
cd "$(dirname "$0")/.." || exit 2
command -v go > /dev/null || exit 2
lib=$PWD/build/libaletheia-ffi.so
[ -f "$lib" ] || exit 2

# Python names each subcommand on the line after it opens the subparser; Go
# names each on a case of the dispatch. The three spellings of help are the one
# thing neither takes from the other, so they are left out of the comparison.
python_commands() {
	grep -A1 'subparsers.add_parser($' python/aletheia/cli.py |
		grep -oE '"[a-z-]+"' | tr -d '"' | sort -u
}
go_commands() {
	sed -n '/switch cmd {/,/^	}/p' go/cmd/aletheia/main.go |
		grep -oE '^	case .*' | grep -oE '"[a-z-]+"|"--?[a-z-]+"' | tr -d '"' |
		grep -vxE '\-h|\-\-help|help' | sort -u
}

py=$(python_commands)
go=$(go_commands)
[ -n "$py" ] || { echo "no subcommand was read from the Python interface"; exit 1; }
[ -n "$go" ] || { echo "no subcommand was read from the Go interface"; exit 1; }

missing=$(comm -23 <(printf '%s\n' "$py") <(printf '%s\n' "$go"))
extra=$(comm -13 <(printf '%s\n' "$py") <(printf '%s\n' "$go"))
status=0
if [ -n "$missing" ]; then
	echo "the Go interface does not answer: $(printf '%s' "$missing" | tr '\n' ' ')"
	status=1
fi
if [ -n "$extra" ]; then
	echo "the Go interface answers what Python does not: $(printf '%s' "$extra" | tr '\n' ' ')"
	status=1
fi

work=$(mktemp -d) || exit 2
trap 'rm -rf "$work"' EXIT
(cd go && go build -o "$work/aletheia" ./cmd/aletheia/) || exit 2
export ALETHEIA_LIB=$lib LD_LIBRARY_PATH=$PWD/build
"$work/aletheia" check > /dev/null 2> "$work/stderr.txt"
if ! grep -q "'check' is not available" "$work/stderr.txt"; then
	echo "check is not refused by name:"
	head -2 "$work/stderr.txt" | sed 's/^/  /'
	status=1
fi

[ "$status" -eq 0 ] || exit 1
echo "PASS: the Go interface answers the Python subcommands and names the one it refuses"
