#!/usr/bin/env bash
# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
#
# Probes docs/development/BUILDING.md, its two "Runtime, Rust layer" tables.
# Claim: the Rust ledger names every crate the [dependencies] tables of
# rust/Cargo.toml and rust/excel/Cargo.toml declare (the binding's own crate
# excluded), and no other, and each row's licence is the one cargo metadata
# records for the crate (read offline from the local registry cache).
# Non-zero exit: a declared crate is missing from the tables, a row names a
# crate neither manifest declares, or a row's licence differs from cargo's.
# Exit 2 when cargo cannot read the metadata offline.
set -u
cd "$(dirname "$0")/.." || exit 2
doc=docs/development/BUILDING.md
[ -f "$doc" ] || exit 2
tables=$(sed -n '/^### Runtime, Rust layer/,/^### Runtime, Python/p' "$doc" | grep -E '^\| [a-z]' | grep -v '^| Crate')
[ -n "$tables" ] || { echo "$doc has no Rust ledger table"; exit 1; }
declared=$(for m in rust/Cargo.toml rust/excel/Cargo.toml; do sed -n '/^\[dependencies\]/,/^\[/p' "$m" | grep -oE '^[a-z][a-z0-9_-]+ *=' | sed 's/ *=//'; done | grep -vx aletheia | sort -u)
[ -n "$declared" ] || { echo "the Cargo manifests declare no dependency"; exit 2; }
listed=$(printf '%s\n' "$tables" | cut -d'|' -f2 | sed 's/^ *//; s/ *$//' | sort -u)
status=0
for c in $declared; do printf '%s\n' "$listed" | grep -qx "$c" || { echo "declared but not in the ledger: $c"; status=1; }; done
for c in $listed; do printf '%s\n' "$declared" | grep -qx "$c" || { echo "in the ledger but not declared: $c"; status=1; }; done
recorded=$(for d in rust rust/excel; do (cd "$d" && cargo metadata --format-version 1 --offline 2>/dev/null); done \
    | python/.venv/bin/python -c 'import json,sys
seen={}
for line in sys.stdin:
    for p in json.loads(line)["packages"]:
        seen.setdefault(p["name"], p["license"])
for n,l in seen.items(): print(n, l)')
[ -n "$recorded" ] || { echo "cargo metadata --offline read nothing; the registry cache is empty"; exit 2; }
while IFS='|' read -r _ name lic _; do
    name=$(printf '%s' "$name" | sed 's/^ *//; s/ *$//'); lic=$(printf '%s' "$lic" | sed 's/^ *//; s/ *$//')
    got=$(printf '%s\n' "$recorded" | awk -v n="$name" '$1==n{$1=""; sub(/^ /,""); print}')
    [ "$got" = "$lic" ] || { echo "$name: the ledger says '$lic', cargo records '$got'"; status=1; }
done <<< "$tables"
[ "$status" -eq 0 ] && echo "PASS: the ledger and the Cargo manifests name the same $(printf '%s\n' "$declared" | wc -l) crates, each with the licence cargo records"
exit "$status"
