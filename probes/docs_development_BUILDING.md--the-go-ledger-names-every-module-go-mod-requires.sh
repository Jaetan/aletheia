#!/usr/bin/env bash
# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
#
# Probes docs/development/BUILDING.md, its "Runtime, Go layer" table.
# Claim: the Go dependency ledger names every direct third-party module the Go
# modules require (the go.mod of every module go/go.work uses, indirect
# requirements and the project's own modules excluded), and no other.
# Non-zero exit: a required module is missing from the table, or a row names a
# module no go.mod requires. Exits 2 without Go.
set -u
cd "$(dirname "$0")/.." || exit 2
command -v go > /dev/null || exit 2
modules=$(cd go && go list -m -f '{{.Dir}}') || exit 2
[ -n "$modules" ] || exit 2
doc=docs/development/BUILDING.md
[ -f "$doc" ] || exit 2
table=$(sed -n '/^### Runtime, Go layer/,/^### /p' "$doc" | grep -E '^\| [a-z]' | grep -v '^| Module')
[ -n "$table" ] || { echo "$doc has no Go ledger table"; exit 1; }
required=$(for dir in $modules; do cat "$dir/go.mod"; done | grep -vE '// indirect' | grep -oE '^\s*(require )?[a-z][A-Za-z0-9./-]+ v[0-9][^ ]*' | awk '{print $(NF-1)}' | grep -v '^github.com/Jaetan/aletheia' | sort -u)
[ -n "$required" ] || { echo "the go.mod files require nothing"; exit 2; }
listed=$(printf '%s\n' "$table" | cut -d'|' -f2 | sed 's/^ *//; s/ *$//' | sort -u)
status=0
for m in $required; do printf '%s\n' "$listed" | grep -qx "$m" || { echo "required but not in the ledger: $m"; status=1; }; done
for m in $listed; do printf '%s\n' "$required" | grep -qx "$m" || { echo "in the ledger but not required: $m"; status=1; }; done
[ "$status" -eq 0 ] && echo "PASS: the ledger and the go.mod files name the same $(printf '%s\n' "$required" | wc -l) modules"
exit "$status"
