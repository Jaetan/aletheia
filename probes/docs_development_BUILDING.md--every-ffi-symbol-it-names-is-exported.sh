#!/usr/bin/env bash
# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
#
# Probes docs/development/BUILDING.md.
# Claim: every aletheia_<name> symbol the guide names is a foreign export of
# haskell-shim/src/AletheiaFFI.hs. The MAlonzo troubleshooting entry used to
# name aletheia_process_json, which the shim never exported.
# Non-zero exit: the guide names a symbol the shim does not export.
set -u
cd "$(dirname "$0")/.." || exit 2
doc=docs/development/BUILDING.md
[ -f "$doc" ] || exit 2
named=$(grep -oE '\baletheia_[a-z_]+' "$doc" | sort -u)
[ -n "$named" ] || { echo "$doc names no FFI symbol; the probe would pass vacuously"; exit 2; }
exported=$(grep -oE 'foreign export ccall aletheia_[a-z_]+' haskell-shim/src/AletheiaFFI.hs | awk '{print $NF}' | sort -u)
status=0
for s in $named; do
    printf '%s\n' "$exported" | grep -qx "$s" || { echo "not exported by the shim: $s"; status=1; }
done
[ "$status" -eq 0 ] && echo "PASS: all $(printf '%s\n' "$named" | wc -l) symbols the guide names are exported"
exit "$status"
