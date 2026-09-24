#!/usr/bin/env bash
# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
#
# Probes docs/development/BUILDING.md, its "Runtime, Haskell layer" table.
# Claim: the Haskell rows of the ledger are exactly the GHC packages
# libaletheia-ffi.so links, as ldd lists them (libHS<name>-<version>...so),
# each row's licence is what ghc-pkg records for the package, and the system
# libraries it names are the non-GHC libraries ldd lists. The library is
# build/libaletheia-ffi.so, or the path ALETHEIA_LIB names.
# Non-zero exit: a linked package is missing from the ledger, a ledger row
# names a package the library does not link, or a row's licence differs from
# ghc-pkg's. Exit 2 without a built library.
set -u
cd "$(dirname "$0")/.." || exit 2
doc=docs/development/BUILDING.md
[ -f "$doc" ] || exit 2
lib=${ALETHEIA_LIB:-build/libaletheia-ffi.so}
[ -f "$lib" ] || { echo "no built library at $lib; build first or set ALETHEIA_LIB"; exit 2; }
table=$(sed -n '/^### Runtime, Haskell layer/,/^System libraries/p' "$doc" | grep -E '^\| [A-Za-z]' | grep -v '^| Package')
[ -n "$table" ] || { echo "$doc has no Haskell ledger table"; exit 1; }
linked=$(ldd "$lib" | grep -oE 'libHS[a-z-]+-[0-9]' | sed 's/^libHS//; s/-[0-9]$//' | sort -u)
[ -n "$linked" ] || { echo "ldd lists no Haskell package for $lib"; exit 2; }
listed=$(printf '%s\n' "$table" | cut -d'|' -f2 | sed 's/^ *//; s/ *$//; s/^GHC RTS$/rts/' | sort -u)
status=0
for p in $linked; do printf '%s\n' "$listed" | grep -qx "$p" || { echo "linked but not in the ledger: $p"; status=1; }; done
for p in $listed; do printf '%s\n' "$linked" | grep -qx "$p" || { echo "in the ledger but not linked: $p"; status=1; }; done
while IFS='|' read -r _ name lic _; do
    name=$(printf '%s' "$name" | sed 's/^ *//; s/ *$//; s/^GHC RTS$/rts/'); lic=$(printf '%s' "$lic" | sed 's/^ *//; s/ *$//')
    recorded=$(ghc-pkg field "$name" license 2>/dev/null | awk '{print $2}')
    [ -n "$recorded" ] || { echo "ghc-pkg records no licence for $name"; status=1; continue; }
    [ "$recorded" = "$lic" ] || { echo "$name: the ledger says $lic, ghc-pkg records $recorded"; status=1; }
done <<< "$table"
for l in gmp ffi c; do
    ldd "$lib" | grep -q "lib$l\.so" || { echo "the ledger names lib$l, ldd does not list it"; status=1; }
done
[ "$status" -eq 0 ] && echo "PASS: the ledger names the $(printf '%s\n' "$linked" | wc -l) Haskell packages ldd lists, each with the licence ghc-pkg records"
exit "$status"
