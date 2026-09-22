#!/usr/bin/env bash
# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
#
# Probes cpp/tests/unit_tests_json.cpp.
# Claim: the test that nests a formula past the serializer's depth bound reads
# no frame that has returned. Its alternatives come from a Catch2 generator,
# which is built once and serves them on the later entries of the body, so an
# alternative holding a reference into the frame it was built in reads a
# returned frame from the second entry on. The suite passes either way: only
# the address sanitizer says so, and no lane of the repository runs one over
# this binary, so the reading is this probe's.
# The sanitizer's stack-use-after-return detection is asked for by name rather
# than taken from the runtime's default, so the probe reads the same whatever
# that default is.
# Non-zero exit: the test fails, or the sanitizer reports against it. Exits 0
# with a note when no address-sanitizer tree is configured.
set -u
cd "$(dirname "$0")/.." || exit 2
tree=cpp/build-asan
cache=$tree/CMakeCache.txt
[ -f "$cache" ] || { echo "no $tree configured, claim untestable"; exit 0; }
grep -q '^ALETHEIA_SANITIZER:STRING=address$' "$cache" || {
    echo "$tree is not an address-sanitizer tree, claim untestable"
    exit 0
}
log=$tree/probe-scratch/nesting-test.log
mkdir -p "$(dirname "$log")" || exit 2
# One core is left free, since the machine is somebody's to use while a
# probe runs.
cmake --build "$tree" --target unit_tests -j"$(($(nproc) - 1))" > "$log" 2>&1 || {
    echo "the address-sanitizer unit tests do not build:"
    tail -20 "$log"
    exit 2
}
ASAN_OPTIONS=detect_stack_use_after_return=1 \
    "$tree/unit_tests" \
    "serialize_set_properties refuses a formula nested past the depth bound" \
    > "$log" 2>&1
rc=$?
grep -q "AddressSanitizer" "$log" && {
    echo "the address sanitizer reports against the nesting test:"
    grep -m3 "AddressSanitizer\|#0 \|#1 " "$log"
    exit 1
}
[ "$rc" -eq 0 ] || {
    echo "the nesting test exits $rc under the address sanitizer:"
    tail -20 "$log"
    exit 1
}
exit 0
