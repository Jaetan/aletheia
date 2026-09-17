#!/usr/bin/env bash
# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
#
# Probes the six stringer outputs of go/aletheia:
#   go/aletheia/byteorder_string.go, go/aletheia/dbcattrscope_string.go,
#   go/aletheia/dbcvartype_string.go, go/aletheia/errorkind_string.go,
#   go/aletheia/issueseverity_string.go, go/aletheia/verdict_string.go.
# Claim: each tracked file is byte for byte what its own go:generate directive
# produces from the package as it stands, so no constant was added, renamed
# or re-commented without regenerating, and no hand edit sits in a file that
# says DO NOT EDIT. No gate runs go generate, which is why this probe exists.
# Non-zero exit: a directive names a file that differs from the generator's
# output, or a generated file has no directive. Exits 2 when stringer is not
# on PATH (go install golang.org/x/tools/cmd/stringer@latest).
set -u
cd "$(dirname "$0")/.." || exit 2
export PATH=$HOME/go/bin:$PATH
command -v stringer > /dev/null || exit 2
scratch=$(mktemp -d)
trap 'rm -rf "$scratch"' EXIT
status=0
seen=0
cd go/aletheia || exit 2
while IFS= read -r line; do
    # the directive, verbatim, with its -output redirected to the scratch dir
    args=${line#*stringer }
    out=$(printf '%s\n' "$args" | sed -n 's/.*-output=\([^ ]*\).*/\1/p')
    [ -n "$out" ] || { echo "directive without -output: $line"; status=1; continue; }
    seen=$((seen + 1))
    # shellcheck disable=SC2086
    stringer ${args%-output=*} -output="$scratch/$out" || { echo "stringer failed for $out"; status=1; continue; }
    # the header quotes the -output path verbatim, so the scratch prefix is
    # removed before the comparison; everything else must be byte-identical
    sed "s|$scratch/||" "$scratch/$out" > "$scratch/$out.norm"
    if ! cmp -s "$out" "$scratch/$out.norm"; then
        echo "$out differs from what its directive generates:"
        diff "$out" "$scratch/$out.norm" | head -10
        status=1
    fi
done < <(grep -h '^//go:generate stringer' ./*.go)
for f in *_string.go; do
    grep -q "output=$f" ./*.go || { echo "$f has no go:generate directive"; status=1; }
done
[ "$seen" -gt 0 ] || { echo "no stringer directive found; the claim is untestable"; exit 1; }
[ "$status" -eq 0 ] && echo "PASS: all $seen stringer outputs match their directives"
exit $status
