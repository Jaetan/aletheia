#!/usr/bin/env bash
# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
#
# Probes go/cmd/aletheia/main.go.
# Claim: when a subcommand's JSON report cannot be written the CLI exits with
# its error code and says so. A caller redirects this stream into a file and
# reads it back, so an exit of zero over a truncated report is read as a run
# that succeeded. Every subcommand that writes one is checked, since each
# reaches the writer by its own path.
# The write is made to fail by sending it to /dev/full, which accepts an open
# and refuses every write with ENOSPC.
# Non-zero exit: a subcommand reported success without writing its report.
# Exits 2 without Go, without a built kernel, or without /dev/full.
set -u
cd "$(dirname "$0")/.." || exit 2
command -v go > /dev/null || exit 2
lib=$PWD/build/libaletheia-ffi.so
[ -f "$lib" ] || exit 2
[ -c /dev/full ] || exit 2
dbc=python/tests/fixtures/dbc_corpus/minimal.dbc
[ -f "$dbc" ] || exit 2

work=$(mktemp -d) || exit 2
trap 'rm -rf "$work"' EXIT
(cd go && go build -o "$work/aletheia" ./cmd/aletheia/) || exit 2

export ALETHEIA_LIB=$lib LD_LIBRARY_PATH=$PWD/build
failed=0
check() {
	"$work/aletheia" "$@" > /dev/full 2> "$work/stderr.txt"
	status=$?
	if [ "$status" -eq 0 ]; then
		echo "reported success with nowhere to write: $*"
		failed=1
	elif ! grep -q "writing the report" "$work/stderr.txt"; then
		echo "failed without saying the report could not be written: $*"
		tail -2 "$work/stderr.txt" | sed 's/^/    /'
		failed=1
	fi
}
check validate --dbc "$dbc" --json
check signals --dbc "$dbc" --json
# format-dbc has no --json: canonical JSON is the whole of what it emits.
check format-dbc --dbc "$dbc"
check extract --dbc "$dbc" 0x100 0000000000000000 --json
check mux-query --dbc "$dbc" 0x100 --json

[ "$failed" -eq 0 ] || exit 1
echo "PASS: a report that cannot be written exits with an error and says so"
