#!/usr/bin/env bash
# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
#
# Probes tools/build_python.sh.
# Claim: a release series with no Sigstore identity recorded in the script is
# refused before anything is fetched, so a tarball is only ever verified
# against the identity python.org publishes for its series, never against a
# guessed one. The probe asks for a series no table row names and needs no
# network: the refusal comes before the download.
# Non-zero exit: the script did not exit 1 with its refusal for that series.
set -u
cd "$(dirname "$0")/.." || exit 2
log=$(mktemp) || exit 2
trap 'rm -f "$log"' EXIT
tools/build_python.sh 3.99.0 "$(mktemp -u)" > "$log" 2>&1
status=$?
out=$(cat "$log")
expected="build_python: no signing identity recorded for 3.99; add it from python.org's Sigstore page"
if [ "$status" -ne 1 ] || [ "$out" != "$expected" ]; then
    printf 'exit %s, output:\n%s\n' "$status" "$out"
    exit 1
fi
