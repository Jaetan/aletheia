#!/usr/bin/env bash
# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
#
# Probes go/aletheia/ffi_nocgo.go.
# Claim: the Go module builds with CGO_ENABLED=0, which is the whole reason the
# stub exists. The binding's verification steps list the command, but the
# orchestrator does not run it, so until it does this probe is what holds the
# claim. The build covers the commands and the benchmarks, not only the
# package, since those are the consumers a missing stub breaks.
# Non-zero exit: something in the module needs cgo. Exits 2 without Go.
set -u
cd "$(dirname "$0")/../go" || exit 2
command -v go > /dev/null || exit 2
out=$(CGO_ENABLED=0 go build ./... 2>&1)
if [ -n "$out" ]; then
	echo "the module does not build without cgo:"
	printf '%s\n' "$out" | head -20 | sed 's/^/  /'
	exit 1
fi
echo "PASS: the module builds with CGO_ENABLED=0"
