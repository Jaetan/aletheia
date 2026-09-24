#!/usr/bin/env bash
# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
#
# Probes go/.gremlins.yaml.
# Claim: the six mutators gremlins ships off by default (inverted
# assignments, bitwise operators, bitwise assignments, logical operators and
# loop control, and removed self-assignments) are on, and it is this file that
# turns them on. A dry run of gremlins from go/ lists a mutant of each of the
# six kinds; the same dry run with one kind turned off from the environment,
# which gremlins reads ahead of the file, lists none of that kind, which is
# what shows the file is doing the turning on. Non-zero exit: a kind has no
# mutant with the file in force, or the overridden kind still has one. Exits
# 0 with a note when gremlins is not installed, the claim being untestable.
set -u
cd "$(dirname "$0")/.." || exit 2
export PATH="$PATH:$HOME/go/bin"
command -v gremlins > /dev/null || { echo "gremlins not installed, claim untestable"; exit 0; }
lib="$PWD/build/libaletheia-ffi.so"
[ -f "$lib" ] || exit 2
with=$(cd go && ALETHEIA_LIB="$lib" gremlins unleash --dry-run ./aletheia 2>&1) || {
    echo "the dry run did not run"; exit 1; }
without=$(cd go && GREMLINS_MUTANTS_INVERT_LOGICAL_ENABLED=false ALETHEIA_LIB="$lib" \
    gremlins unleash --dry-run ./aletheia 2>&1) || {
    echo "the dry run with one kind overridden did not run"; exit 1; }
status=0
for kind in INVERT_ASSIGNMENTS INVERT_BITWISE INVERT_BWASSIGN INVERT_LOGICAL INVERT_LOOPCTRL REMOVE_SELF_ASSIGNMENTS; do
    n=$(printf '%s\n' "$with" | grep -c " $kind at ")
    [ "$n" -gt 0 ] || { echo "no $kind mutant with the file in force"; status=1; }
done
still=$(printf '%s\n' "$without" | grep -c " INVERT_LOGICAL at ")
[ "$still" -eq 0 ] || { echo "$still INVERT_LOGICAL mutants with the kind overridden off, so the file is not what turns it on"; status=1; }
[ "$status" -eq 0 ] && echo "PASS: the six default-off kinds each carry a mutant, and the override removes one kind"
exit $status
