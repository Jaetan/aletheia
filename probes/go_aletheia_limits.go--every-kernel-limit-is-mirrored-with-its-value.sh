#!/usr/bin/env bash
# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
#
# Probes go/aletheia/limits.go against src/Aletheia/Limits.agda.
# Claim: every numeric limit the kernel defines has a mirror in the binding
# carrying the same value. The binding says it mirrors the kernel exactly, and
# nothing compiles the two lists together: a limit added to the kernel, or a
# value changed on either side, would leave the binding refusing at a different
# size than the kernel does, or not refusing at all. The check compiles a
# program against the package, so a missing mirror is a name that does not
# exist rather than a grep that finds nothing. Non-zero exit: a kernel limit
# has no mirror, or a mirror carries another value. Exits 2 without Go.
set -u
cd "$(dirname "$0")/.." || exit 2
command -v go > /dev/null || exit 2
limits=src/Aletheia/Limits.agda
[ -f "$limits" ] || { echo "missing $limits"; exit 2; }

scratch=$(mktemp -d) || exit 2
trap 'rm -rf "$scratch"' EXIT

# The kernel writes its limits in kebab case; the binding writes the same names
# in camel case, with some words fully capitalised. Comparing them with the
# separators removed and the case folded away pairs them without a table.
mapfile -t pairs < <(grep -oP '^max-[a-z-]+ = [0-9]+' "$limits" | sed 's/ = /\t/')
[ "${#pairs[@]}" -gt 0 ] || { echo "no limit found in $limits"; exit 1; }

go_names=$(grep -oP '^\tMax[A-Za-z]+(?= =)' go/aletheia/limits.go | tr -d '\t')
{
	echo 'package main'
	echo
	echo 'import ('
	echo '	"fmt"'
	echo
	echo '	"github.com/Jaetan/aletheia/go/v5/aletheia"'
	echo ')'
	echo
	echo 'func main() {'
	for n in $go_names; do
		printf '\tfmt.Printf("%%s %%d\\n", "%s", uint64(aletheia.%s))\n' "$n" "$n"
	done
	echo '}'
} > "$scratch/main.go"

cp "$scratch/main.go" go/probe_limits_main.go.tmp
mkdir -p go/probe-limits
mv go/probe_limits_main.go.tmp go/probe-limits/main.go
values=$(cd go && go run ./probe-limits 2>&1)
rc=$?
rm -rf go/probe-limits
if [ $rc -ne 0 ]; then
	echo "the binding's limits do not compile:"
	printf '%s\n' "$values" | head -5 | sed 's/^/  /'
	exit 1
fi

status=0
seen=0
for entry in "${pairs[@]}"; do
	name=${entry%%	*}
	value=${entry##*	}
	folded=$(printf '%s' "$name" | tr -d '-' | tr 'A-Z' 'a-z')
	line=$(printf '%s\n' "$values" | while read -r gname gvalue; do
		if [ "$(printf '%s' "$gname" | tr 'A-Z' 'a-z')" = "$folded" ]; then
			printf '%s %s\n' "$gname" "$gvalue"
		fi
	done)
	if [ -z "$line" ]; then
		echo "the kernel's $name has no mirror in the binding"
		status=1
		continue
	fi
	seen=$((seen + 1))
	got=${line##* }
	if [ "$got" != "$value" ]; then
		echo "${line%% *} is $got, and the kernel's $name is $value"
		status=1
	fi
done

if [ $status -eq 0 ]; then
	echo "PASS: all $seen kernel limits are mirrored with their values"
fi
exit $status
