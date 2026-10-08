#!/usr/bin/env bash
# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
#
# Probes Shakefile.hs.
# Claim: the stand-in kernels the build makes are the ones the tests load, and
# each exports what its role needs. Every name a binding's test loads (Go's
# standIn, Python's StandInName, Rust's stand_in::stand_in and the C++ build's
# ALETHEIA_STAND_IN_DIR paths) is in the Shakefile's standIns table, and every
# entry of the table is loaded by some test. After a build, every entry is under
# build/stand-ins: the stale and the ABI-only kernels export
# aletheia_abi_version alone of the kernel's symbols, symbolless exports none of
# them, and null_kernel and recording_kernel export every one the library does.
# Non-zero exit: a name is on one side only, a built stand-in is missing, or one
# exports other than its role. Exits 2 when the names cannot be read, or, past
# the names, without a built library or nm.
set -u
cd "$(dirname "$0")/.." || exit 2
for file in Shakefile.hs cpp/CMakeLists.txt; do [ -f "$file" ] || exit 2; done

names() { grep -o '"[a-z_]*"' | tr -d '"' | grep -vx 'so' | sort -u; }
table=$(sed -n '/^standIns = /,/\]/p' Shakefile.hs | names)
loaded=$({
	grep -oh 'standIn(t, lib, "[a-z_]*")' go/aletheia/*_test.go
	grep -oh 'StandInName("[a-z_]*")' python/tests/*.py
	grep -oh 'stand_in::stand_in("[a-z_]*")' rust/tests/*.rs
	grep -o 'ALETHEIA_STAND_IN_DIR}/[a-z_]*\.so' cpp/CMakeLists.txt | sed 's|.*/\([a-z_]*\)\.so|"\1"|'
} | names)
[ -n "$table" ] && [ -n "$loaded" ] || { echo "no stand-in name read from the table or the tests"; exit 2; }
unbuilt=$(comm -13 <(printf '%s\n' "$table") <(printf '%s\n' "$loaded"))
unloaded=$(comm -23 <(printf '%s\n' "$table") <(printf '%s\n' "$loaded"))
if [ -n "$unbuilt" ] || [ -n "$unloaded" ]; then
	[ -n "$unbuilt" ] && echo "loaded by a test but not in the Shakefile's table: $unbuilt"
	[ -n "$unloaded" ] && echo "in the Shakefile's table but loaded by no test: $unloaded"
	exit 1
fi

lib=build/libaletheia-ffi.so
[ -f "$lib" ] || exit 2
command -v nm > /dev/null || exit 2
exports() { nm -D --defined-only "$1" | awk '{print $3}' | grep '^aletheia_' | sort -u; }
kernel=$(exports "$lib")
status=0
for name in $table; do
	stand_in=build/stand-ins/$name.so
	if [ ! -f "$stand_in" ]; then
		echo "$stand_in is not built"
		status=1
		continue
	fi
	own=$(comm -12 <(exports "$stand_in") <(printf '%s\n' "$kernel") | paste -sd' ')
	case $name in
	stale_abi_kernel | abi_only_kernel) want=aletheia_abi_version ;;
	symbolless) want= ;;
	null_kernel | recording_kernel) want=$(printf '%s\n' "$kernel" | paste -sd' ') ;;
	*)
		echo "$name: a stand-in this probe knows no role for"
		status=1
		continue
		;;
	esac
	if [ "$own" != "$want" ]; then
		echo "$name exports, of the kernel's symbols: ${own:-none}; its role needs: ${want:-none}"
		status=1
	fi
done
[ "$status" -eq 0 ] && echo "PASS: every stand-in a test loads is in the build's table and built, each exporting what its role needs"
exit "$status"
