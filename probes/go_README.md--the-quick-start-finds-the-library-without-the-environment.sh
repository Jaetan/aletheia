#!/usr/bin/env bash
# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
#
# Probes go/README.md.
# Claim: the quick start's second command, `cd go && go test ./aletheia/`,
# runs the real-library tests with no ALETHEIA_LIB in the environment, because
# the binding's library search falls back to the build tree relative to the
# package directory. A test that would skip without the library must not skip.
# Non-zero exit: the doc-example harness skipped for want of the library, or
# the run failed. Exits 2 when build/libaletheia-ffi.so or Go is missing.
set -u
cd "$(dirname "$0")/.." || exit 2
[ -f build/libaletheia-ffi.so ] || exit 2
command -v go > /dev/null || exit 2
out=$(cd go && env -u ALETHEIA_LIB go test ./aletheia/ -count=1 -run '^TestDocExamples$' -v 2>&1); rc=$?
[ "$rc" -eq 0 ] || { echo "the run failed: $(printf '%s' "$out" | tail -5)"; exit 1; }
case $out in *"--- SKIP: TestDocExamples"*) echo "the harness skipped: the library was not found without the environment"; exit 1 ;; esac
case $out in *"--- PASS: TestDocExamples"*) ;; *) echo "the harness did not report a pass: $(printf '%s' "$out" | tail -3)"; exit 1 ;; esac
echo "PASS: the quick start finds the library from the package directory"
