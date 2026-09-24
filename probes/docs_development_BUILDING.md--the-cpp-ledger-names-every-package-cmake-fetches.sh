#!/usr/bin/env bash
# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
#
# Probes docs/development/BUILDING.md, its "Runtime, C++ layer" table.
# Claim: the C++ dependency ledger names every package cpp/CMakeLists.txt
# fetches through FetchContent, and names no package it does not fetch. The
# ledger used to carry versions beside the names, and every version had rotted
# behind the CMake pins while two fetched packages, miniz and pugixml, were not
# listed at all.
# Non-zero exit: a fetched package is missing from the table, or a table row
# names a package CMake does not fetch.
set -u
cd "$(dirname "$0")/.." || exit 2
doc=docs/development/BUILDING.md
[ -f "$doc" ] || exit 2
table=$(sed -n '/^### Runtime, C++ layer/,/^### /p' "$doc" | grep -E '^\| [A-Za-z]' | grep -v '^| Package')
[ -n "$table" ] || { echo "$doc has no C++ ledger table"; exit 1; }
fetched=$(grep -oE 'FetchContent_Declare\([A-Za-z0-9_-]+' cpp/CMakeLists.txt | sed 's/.*(//; s/_fetch$//' | tr 'A-Z' 'a-z' | sort -u)
[ -n "$fetched" ] || { echo "cpp/CMakeLists.txt declares no FetchContent package"; exit 2; }
listed=$(printf '%s\n' "$table" | cut -d'|' -f2 | tr ',' '\n' | sed 's#.*/##; s/^ *//; s/ *$//' | tr 'A-Z' 'a-z' | sort -u)
status=0
for p in $fetched; do
    printf '%s\n' "$listed" | grep -qx "$p" || { echo "fetched but not in the ledger: $p"; status=1; }
done
for p in $listed; do
    printf '%s\n' "$fetched" | grep -qx "$p" || { echo "in the ledger but not fetched: $p"; status=1; }
done
[ "$status" -eq 0 ] && echo "PASS: the ledger and cpp/CMakeLists.txt name the same $(printf '%s\n' "$fetched" | wc -l) packages"
exit "$status"
