#!/usr/bin/env bash
# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
#
# Probes go/aletheia/check.go.
# Claim: every ThenCondition the package constructs carries a description
# (thenDescParts), so Within can append its " within {ms}ms" suffix
# unconditionally; the empty-description case is unreachable through the
# builders, which is why Within no longer tests for it. Non-zero exit: a
# ThenCondition literal in the package's non-test sources sets no
# thenDescParts, or no literal is found at all.
set -u
cd "$(dirname "$0")/.." || exit 2
status=0
literals=0
for f in go/aletheia/*.go; do
    case $f in *_test.go) continue ;; esac
    # each literal spans from "ThenCondition{" to its closing brace at column one or a lone "}"
    awk -v file="$f" '
        /ThenCondition\{/ { inlit = 1; body = ""; start = NR }
        inlit { body = body $0 "\n" }
        inlit && /^\t*}/ && !/ThenCondition\{/ {
            inlit = 0; count++
            if (body !~ /thenDescParts:/) { printf "%s:%d: ThenCondition without thenDescParts\n", file, start; bad++ }
        }
        END { printf "%d %d\n", count, bad > "/dev/stderr" }
    ' "$f" 2> /tmp/probe_then_$$ || status=1
    read -r count bad < /tmp/probe_then_$$
    rm -f /tmp/probe_then_$$
    literals=$((literals + count))
    [ "$bad" -eq 0 ] || status=1
done
[ "$literals" -gt 0 ] || { echo "no ThenCondition literal found; the claim is untestable"; exit 1; }
[ "$status" -eq 0 ] && echo "PASS: all $literals ThenCondition literals carry a description"
exit $status
