#!/usr/bin/env bash
# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
#
# Probes docs/development/BUILDING.md.
# Claim: every "cabal run shake -- <target>" the guide shows names a phony
# target Shakefile.hs defines, so no command block in the guide invokes a
# target the build system does not have.
# Non-zero exit: the guide names a target Shakefile.hs does not define.
set -u
cd "$(dirname "$0")/.." || exit 2
doc=docs/development/BUILDING.md
[ -f "$doc" ] || exit 2
named=$(grep -oE 'cabal run shake -- [a-z][a-z-]*' "$doc" | awk '{print $NF}' | sort -u)
[ -n "$named" ] || { echo "$doc names no shake target"; exit 2; }
defined=$(grep -oE 'phony "[a-z-]+"' Shakefile.hs | cut -d'"' -f2 | sort -u)
status=0
for t in $named; do
    printf '%s\n' "$defined" | grep -qx "$t" || { echo "not a Shakefile.hs target: $t"; status=1; }
done
[ "$status" -eq 0 ] && echo "PASS: all $(printf '%s\n' "$named" | wc -l) targets the guide names exist"
exit "$status"
