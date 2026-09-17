#!/usr/bin/env bash
# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
#
# Probes go/aletheia, against the claim docs/reference/GO_API.md makes about it.
# Claim: the package panics nowhere. Every fallible call answers an error, which
# is what lets a host embed the binding and report a refusal rather than die of
# one. The guide says so in its error-handling section, and nothing else checks
# it: a panic added to a path no test reaches would make the sentence false and
# fail nothing.
# The test files are not part of the claim; a test may panic to stop itself.
# Non-zero exit: the package panics somewhere. Exits 2 when the package is not
# where this expects it.
set -u
cd "$(dirname "$0")/.." || exit 2
[ -d go/aletheia ] || exit 2

found=$(grep -n "panic(" go/aletheia/*.go 2> /dev/null | grep -v "_test\.go:" || true)
if [ -n "$found" ]; then
	echo "the package panics, where the guide says it does not:"
	printf '%s\n' "$found" | sed 's/^/  /'
	exit 1
fi
echo "PASS: the package panics nowhere outside its tests"
