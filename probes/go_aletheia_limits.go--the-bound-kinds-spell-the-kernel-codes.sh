#!/usr/bin/env bash
# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
#
# Probes go/aletheia/limits.go against src/Aletheia/Limits.agda.
# Claim: every bound-kind constant the Go binding declares spells the wire
# string the kernel's own table emits for that kind, and the two rosters hold
# the same kinds. The binding writes them as string constants and the kernel
# as the arms of a function, so nothing compiles one against the other: a kind
# added to the kernel, or a string mistyped here, travels as far as a caller
# matching on it. Non-zero exit: a kind is missing from either side or spelled
# differently.
set -u
cd "$(dirname "$0")/.." || exit 2
go_file=go/aletheia/limits.go
agda_file=src/Aletheia/Limits.agda
for f in "$go_file" "$agda_file"; do
	[ -f "$f" ] || { echo "missing $f"; exit 1; }
done

# The kernel's arms: boundKindCode <Kind> = "<code>".
kernel=$(grep -oP '^boundKindCode\s+\K\w+(?=\s+=\s+")' "$agda_file" | sort -u)
kernel_pairs=$(grep -oP '^boundKindCode\s+\K\w+\s+=\s+"[a-z_]+"' "$agda_file" |
	sed -E 's/\s+=\s+"/ /; s/"$//' | sort)

# The binding's constants: BoundKind<Kind> = "<code>".
go_pairs=$(grep -oP '^\tBoundKind\K\w+\s*=\s*"[a-z_]+"' "$go_file" |
	sed -E 's/\s*=\s*"/ /; s/"$//' | sort)
go_kinds=$(printf '%s\n' "$go_pairs" | cut -d' ' -f1 | sort -u)

if [ -z "$kernel" ] || [ -z "$go_kinds" ]; then
	echo "one side yielded no bound kind; the probe is reading it wrong"
	exit 1
fi

if [ "$kernel_pairs" = "$go_pairs" ]; then
	echo "PASS: the same $(printf '%s\n' "$go_pairs" | wc -l) bound kinds, spelled alike"
	exit 0
fi

echo "the bound kinds differ between the binding and the kernel"
diff <(printf '%s\n' "$kernel_pairs") <(printf '%s\n' "$go_pairs") |
	sed 's/^</  kernel: /; s/^>/  binding: /'
exit 1
