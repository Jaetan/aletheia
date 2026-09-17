#!/usr/bin/env bash
# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
#
# Probes go/aletheia/byteorder_string.go.
# Claim: the two names the stringer output renders for ByteOrder, taken from
# the line comments on the constants in go/aletheia/types.go, are the two
# byte-order names go/aletheia/json.go writes to and reads from the wire, so
# String() and the wire agree even though json.go spells the names by hand.
# Non-zero exit: a name in the generated table is absent from the serializer
# or the parser, or the constant block has no line-commented names.
set -u
cd "$(dirname "$0")/.." || exit 2
status=0
names=$(awk '/^\/\/go:generate stringer -type=ByteOrder/{f=1} f && /^\)/{exit} f && /\/\/ [a-z_]+$/{sub(/.*\/\/ /, ""); print}' go/aletheia/types.go)
[ -n "$names" ] || { echo "no line-commented ByteOrder constants found"; exit 1; }
for n in $names; do
    grep -q "^const _ByteOrder_name = \".*$n.*\"" go/aletheia/byteorder_string.go || { echo "$n is not in the generated name table"; status=1; }
    grep -q "\"byteOrder\"\] = \"$n\"" go/aletheia/json.go || { echo "the serializer never writes $n"; status=1; }
    grep -q "case \"$n\":" go/aletheia/json.go || { echo "the parser never reads $n"; status=1; }
done
[ "$status" -eq 0 ] && echo "PASS: the ByteOrder names and the wire names agree ($(printf '%s\n' "$names" | wc -l) names)"
exit $status
