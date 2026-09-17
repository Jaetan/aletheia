#!/usr/bin/env bash
# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
#
# Probes cpp/tests/.clang-tidy.
# Claim: every check the test configuration disables still fires over the test
# sources, so a disable left behind after its cause was removed is visible
# rather than inherited. The threshold is one finding, not the count recorded
# beside each entry, because that count moves with every test added. Non-zero
# exit: a disabled check reports nothing and no longer earns its place.
set -u
cd "$(dirname "$0")/.." || exit 2
command -v run-clang-tidy-23 > /dev/null || { echo "run-clang-tidy-23 not installed"; exit 0; }
[ -f cpp/build/compile_commands.json ] || { echo "no compile database; configure cpp/build"; exit 2; }
checks=$(sed -n '/^Checks: >/,/^$/p' cpp/tests/.clang-tidy \
    | grep -oE '^\s*-[a-z][A-Za-z0-9*.-]*' | sed 's/^ *-//')
[ -n "$checks" ] || { echo "the test configuration disables nothing"; exit 1; }
joined=$(printf '%s\n' "$checks" | paste -sd, -)
out=$(cd cpp && run-clang-tidy-23 -quiet -p build -checks="-*,$joined" cpp/tests/ 2>&1)
status=0
for check in $checks; do
    if ! printf '%s\n' "$out" | grep -qE "\[[^]]*${check}[,]?[^]]*\]$"; then
        echo "$check is disabled for the tests but reports nothing over them"
        status=1
    fi
done
exit $status
