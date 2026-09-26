#!/usr/bin/env bash
# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
#
# Probes go/aletheia.
# Claim: the functions whose lines the Go mutation record once counted as
# unreached are wholly executed by the suite: the invalid-UTF-8 refusals and
# the definition's marshal, the refusal message's rational, the library
# search and the standalone symbol loading with its dlopen and dlsym
# failures, a kernel entry's dlsym failure and a null answer, the
# enrichment's fallback, the definition constructor and the batch's
# satisfactions. Read off go's own cover profile, per function, so a test
# deleted later reads here as a function no longer wholly reached.
# Non-zero exit: one of those functions is under one hundred percent.
# Exits 2 when the kernel is not built, since the suite loads it.
set -u
cd "$(dirname "$0")/.." || exit 2
[ -f build/libaletheia-ffi.so ] || exit 2
scratch=$(mktemp -d) || exit 2
trap 'rm -rf "$scratch"' EXIT

(cd go && ALETHEIA_LIB="$PWD/../build/libaletheia-ffi.so" \
    go test ./aletheia/ -count=1 -covermode=atomic -coverprofile="$scratch/cover.out" > "$scratch/test.log" 2>&1) || {
    echo "the suite failed:"
    tail -5 "$scratch/test.log" | sed 's/^/  /'
    exit 2
}
(cd go && go tool cover -func="$scratch/cover.out") > "$scratch/func.txt" || exit 2

status=0
for fn in refuseInvalidUTF8 MarshalJSON formatRationalExact findFFILibrary loadStandaloneSymbols \
          rendererDlsym loadSym stringResult Init formatObservedBase NewDBCDefinition Satisfactions \
          FirstViolation parseUnresolvedValueDescs; do
    line=$(grep -E "aletheia/[a-z_]+\.go:[0-9]+:\s+${fn}\s" "$scratch/func.txt" | head -1)
    [ -n "$line" ] || { echo "no function named $fn in the profile"; status=1; continue; }
    echo "$line" | grep -qE '\s100\.0%$' || { echo "not wholly reached: $line"; status=1; }
done
exit $status
