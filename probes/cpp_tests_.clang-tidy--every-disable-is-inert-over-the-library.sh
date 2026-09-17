#!/usr/bin/env bash
# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
#
# Probes cpp/tests/.clang-tidy.
# Claim: every check the test configuration disables is inert over the library
# sources, so none of them is a library finding parked in the test tree. The
# check list is read from the configuration itself, so a check added there is
# covered without editing this probe. Non-zero exit: one of the disabled
# checks reports over cpp/src.
set -u
cd "$(dirname "$0")/.." || exit 2
command -v run-clang-tidy-23 > /dev/null || { echo "run-clang-tidy-23 not installed"; exit 0; }
[ -f cpp/build/compile_commands.json ] || { echo "no compile database; configure cpp/build"; exit 2; }
checks=$(sed -n '/^Checks: >/,/^$/p' cpp/tests/.clang-tidy \
    | grep -oE '^\s*-[a-z][A-Za-z0-9*.-]*' | sed 's/^ *-//' | paste -sd, -)
[ -n "$checks" ] || { echo "the test configuration disables nothing"; exit 1; }
out=$(cd cpp && run-clang-tidy-23 -quiet -p build -checks="-*,$checks" cpp/src/ 2>&1)
found=$(printf '%s\n' "$out" | grep -cE '(warning|error):')
if [ "$found" -ne 0 ]; then
    echo "a check disabled for the tests reports over the library, $found times:"
    printf '%s\n' "$out" | grep -E '(warning|error):' | head -5
    exit 1
fi
exit 0
