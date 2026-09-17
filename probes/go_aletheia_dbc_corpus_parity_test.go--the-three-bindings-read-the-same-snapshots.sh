#!/usr/bin/env bash
# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
#
# Probes go/aletheia/dbc_corpus_parity_test.go.
# Claim: the snapshots it compares against are the ones the Python and C++
# parity tests compare against, the two counterparts it names exist, and the
# corpus is whole: every fixture has a snapshot and every snapshot a fixture.
# Non-zero exit: a counterpart is missing or does not read the snapshot
# directory, or a fixture and its snapshot do not pair up.
set -u
cd "$(dirname "$0")/.." || exit 2
status=0
corpus=python/tests/fixtures/dbc_corpus
snaps=$corpus/parity_snapshots
[ -d "$snaps" ] || { echo "no snapshot directory at $snaps"; exit 1; }
for t in python/tests/test_dbc_corpus_parity.py cpp/tests/dbc_corpus_parity_tests.cpp go/aletheia/dbc_corpus_parity_test.go; do
    [ -f "$t" ] || { echo "$t is missing"; status=1; continue; }
    grep -q "parity_snapshots" "$t" || { echo "$t does not read the snapshot directory"; status=1; }
done
n=0
for dbc in "$corpus"/*.dbc; do
    n=$((n + 1))
    snap=$snaps/$(basename "$dbc" .dbc).json
    [ -f "$snap" ] || { echo "$(basename "$dbc") has no snapshot"; status=1; }
done
for snap in "$snaps"/*.json; do
    dbc=$corpus/$(basename "$snap" .json).dbc
    [ -f "$dbc" ] || { echo "$(basename "$snap") has no fixture"; status=1; }
done
[ "$n" -gt 0 ] || { echo "the corpus is empty"; status=1; }
[ "$status" -eq 0 ] && echo "PASS: $n fixtures, each with its snapshot, read by the three bindings' tests"
exit $status
