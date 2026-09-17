#!/usr/bin/env bash
# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
#
# Probes go/aletheia/types.go against src/Aletheia/DBC/Formatter.agda.
# Claim: the two byte-order names the binding carries, written as the line
# comments the stringer renders and now the single source for both halves of
# the JSON wire, are the names the kernel's formatter emits and its parser
# reads back. The binding and the kernel spell them in different languages, so
# nothing compiles one against the other, and a rename on either side would
# make every signal fail to parse on the far side. Non-zero exit: a name the
# binding carries is not one the kernel formats, or the kernel formats a name
# the binding does not carry.
set -u
cd "$(dirname "$0")/.." || exit 2
go_file=go/aletheia/types.go
formatter=src/Aletheia/DBC/Formatter.agda
for f in "$go_file" "$formatter"; do
	[ -f "$f" ] || { echo "missing $f"; exit 1; }
done

binding=$(awk '/^\/\/go:generate stringer -type=ByteOrder/{f=1} f && /^\)/{exit} f && /\/\/ [a-z_]+$/{sub(/.*\/\/ /, ""); print}' "$go_file" | sort -u)
kernel=$(grep -oP '^formatByteOrder \w+\s*=\s*toList \"\K[a-z_]+' "$formatter" | sort -u)

if [ -z "$binding" ] || [ -z "$kernel" ]; then
	echo "one side yielded no byte-order name; the probe is reading it wrong"
	exit 1
fi
if [ "$binding" = "$kernel" ]; then
	echo "PASS: both spell $(printf '%s ' $binding)"
	exit 0
fi
echo "the byte-order names differ"
diff <(printf '%s\n' "$kernel") <(printf '%s\n' "$binding") | sed 's/^</  kernel: /; s/^>/  binding: /'
exit 1
