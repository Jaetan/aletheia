#!/usr/bin/env bash
# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
#
# Probes go/aletheia/dbc.go.
# Claim: every kernel identifier the type comments cite exists in the Agda
# sources (SignalGroup, varTypeToℕ, AttrScope, formatCANId,
# UnknownValueDescriptionTarget), the six metadata slices of DBCDefinition
# are named after fields the Agda DBC record has, and the doc links in
# square brackets name declarations of the package. Non-zero exit: a cited
# identifier, record field or doc link resolves nowhere.
set -u
cd "$(dirname "$0")/.." || exit 2
f=go/aletheia/dbc.go
status=0
for id in SignalGroup varTypeToℕ AttrScope formatCANId UnknownValueDescriptionTarget; do
    grep -q "$id" "$f" || { echo "the comment no longer cites $id; retire this line of the probe with it"; status=1; continue; }
    git grep -q -F "$id" -- src || { echo "$id is cited but absent from the Agda sources"; status=1; }
done
record=$(awk '/^record DBC : Set where/{f=1; next} f && /^record /{exit} f' src/Aletheia/DBC/Types.agda)
for field in signalGroups environmentVars valueTables nodes comments attributes; do
    grep -q "$field" "$f" || { echo "the DBCDefinition comment no longer names $field"; status=1; continue; }
    printf '%s\n' "$record" | grep -q "^    $field :" || { echo "the Agda DBC record has no field $field"; status=1; }
done
for link in $(grep '^[[:space:]]*//' "$f" | grep -o '\[[A-Z][A-Za-z]*\(\.[A-Za-z]*\)\?\]' | tr -d '[]' | sort -u); do
    t=${link%%.*}
    grep -q "^type $t \|^func $t(" go/aletheia/*.go || { echo "[$link] names no declaration"; status=1; }
done
[ "$status" -eq 0 ] && echo "PASS: every citation in dbc.go resolves"
exit $status
