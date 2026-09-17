#!/usr/bin/env bash
# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
#
# Probes docs/reference/GO_API.md.
# Claim: the shell line the guide prints runs from the directory it names, with
# nothing set in the environment, and lists the signals of the DBC it names. The
# Go fences of this guide are run by the doc-example harness; a shell fence is
# run by nobody, which is how the previous line came to name a library path that
# resolves from neither the directory it tells the reader to stand in nor any
# other.
# The line is read out of the guide rather than copied here, so a guide changed
# without running it fails.
# Non-zero exit: the line is not there, or it does not run. Exits 2 without Go
# or without a built kernel.
set -u
cd "$(dirname "$0")/.." || exit 2
command -v go > /dev/null || exit 2
[ -f build/libaletheia-ffi.so ] || exit 2
guide=docs/reference/GO_API.md
[ -f "$guide" ] || exit 2

line=$(grep -m1 "^go run ./cmd/aletheia " "$guide")
if [ -z "$line" ]; then
	echo "the guide no longer prints a line starting with go run ./cmd/aletheia"
	exit 1
fi

work=$(mktemp -d) || exit 2
trap 'rm -rf "$work"' EXIT
if ! (cd go && unset ALETHEIA_LIB && eval "$line") > "$work/out.txt" 2>&1; then
	echo "the line the guide prints does not run from go/:"
	echo "  $line"
	head -2 "$work/out.txt" | sed 's/^/  /'
	exit 1
fi
if ! grep -q "^Message " "$work/out.txt"; then
	echo "the line ran and listed no message:"
	head -2 "$work/out.txt" | sed 's/^/  /'
	exit 1
fi
echo "PASS: the guide's shell line runs from go/ and lists what the DBC carries"
