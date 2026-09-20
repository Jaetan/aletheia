#!/usr/bin/env bash
# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
#
# Probes .github/workflows/pr-heavy-lanes.yml, the cache step of the Mull
# build, against tools/build_mull.sh.
# Claim: the cache key hashes every file whose content decides what the build
# produces: the build script itself and every patch file under tools/mull/ the
# script applies. A patch edited without an edit to the script would otherwise
# replay the previous binaries from the cache, and the mutation lane would
# sweep with a mutator the tree no longer describes.
# Non-zero exit: a patch the script applies matches no pattern of the key's
# hashFiles call, or the script itself does not, or the key line is missing.
set -u
cd "$(dirname "$0")/.." || exit 2
workflow=.github/workflows/pr-heavy-lanes.yml
script=tools/build_mull.sh
[ -f "$workflow" ] || exit 2
[ -f "$script" ] || exit 2

key=$(grep -E "^\s*key: mull23-.*hashFiles\(" "$workflow") || {
    echo "FAIL: no Mull cache key line with a hashFiles call in $workflow"
    exit 1
}
# The patterns are the quoted arguments of the hashFiles call, in order.
patterns=$(printf '%s\n' "$key" | grep -oE "'[^']+'" | tr -d "'")
[ -n "$patterns" ] || {
    echo "FAIL: the Mull cache key hashes no file: $key"
    exit 1
}

hashed() {
    local path=$1 pattern
    while IFS= read -r pattern; do
        # shellcheck disable=SC2053 # the pattern is meant to glob
        [[ $path == $pattern ]] && return 0
    done <<< "$patterns"
    return 1
}

status=0
hashed "$script" || {
    echo "FAIL: the key does not hash $script"
    status=1
}
applied=$(grep -oE 'mull/[A-Za-z0-9._-]+\.patch' "$script" | sort -u)
[ -n "$applied" ] || {
    echo "FAIL: $script applies no patch under tools/mull/"
    exit 1
}
while IFS= read -r patch; do
    path="tools/$patch"
    [ -f "$path" ] || {
        echo "FAIL: $script applies $path, which is not in the tree"
        status=1
        continue
    }
    hashed "$path" || {
        echo "FAIL: the key does not hash $path"
        status=1
    }
done <<< "$applied"
[ "$status" -eq 0 ] && echo "PASS: the Mull cache key hashes the script and every patch it applies"
exit $status
