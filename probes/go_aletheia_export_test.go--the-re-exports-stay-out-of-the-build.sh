#!/usr/bin/env bash
# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
#
# Probes go/aletheia/export_test.go.
# Claim: each name it re-exports for the tests is declared in that file alone,
# so no file of the production build declares it and no consumer can reach it,
# and the peers it names keep the same helper private: the Rust
# build_diagnostic is crate-private and the Python enrichment module is
# underscore-prefixed. Non-zero exit: a re-exported name is declared by a file
# the build compiles, or a peer helper became public.
set -u
cd "$(dirname "$0")/.." || exit 2
f=go/aletheia/export_test.go
status=0
names=$(grep -oE '^(func|var) [A-Z][A-Za-z0-9_]*' "$f" | awk '{print $2}' | sort -u)
[ -n "$names" ] || { echo "no re-exported name found in $f"; exit 1; }
for n in $names; do
    for src in go/aletheia/*.go; do
        case $src in *_test.go) continue ;; esac
        grep -qE "^(func|var|type) $n\b" "$src" && { echo "$n is declared by $src, which the build compiles"; status=1; }
    done
done
grep -q "pub(crate) fn build_diagnostic" rust/src/enrich.rs || { echo "the Rust build_diagnostic is no longer crate-private"; status=1; }
[ -f python/aletheia/client/_enrichment.py ] || { echo "the Python _enrichment module is gone or renamed"; status=1; }
[ "$status" -eq 0 ] && echo "PASS: all $(printf '%s\n' "$names" | wc -l) re-exports are test-only, and the peers keep theirs private"
exit $status
