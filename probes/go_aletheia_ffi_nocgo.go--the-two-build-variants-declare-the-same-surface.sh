#!/usr/bin/env bash
# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
#
# Probes go/aletheia/ffi_nocgo.go and go/aletheia/decimal_nocgo.go against the
# files the build with cgo compiles in their place.
# Claim: the build without cgo declares every exported name the build with cgo
# declares, and no others, so code calling the package compiles either way
# rather than only the package itself. Each build is the package's non-test
# files under its tag, `cgo && linux` or `!cgo || !linux`, whichever file a
# name lives in. The two sets carry opposite build tags, so the compiler never
# sees them together: a name added to one and forgotten in the other breaks a
# consumer of the other build, silently.
# Non-zero exit: the two surfaces differ, or a build has no file.
set -u
cd "$(dirname "$0")/.." || exit 2
mapfile -t cgo < <(grep -lx '//go:build cgo && linux' go/aletheia/*.go | grep -v '_test\.go$')
mapfile -t nocgo < <(grep -lx '//go:build !cgo || !linux' go/aletheia/*.go | grep -v '_test\.go$')
[ "${#cgo[@]}" -gt 0 ] || { echo "no file carries the cgo build's tag"; exit 1; }
[ "${#nocgo[@]}" -gt 0 ] || { echo "no file carries the build without cgo's tag"; exit 1; }

# Exported functions, and exported methods on the backend, by name.
surface() {
	grep -ohP '^func (\(\w* ?\*?FFIBackend\) )?\K[A-Z]\w*' "$@" | sort -u
}
a=$(surface "${cgo[@]}")
b=$(surface "${nocgo[@]}")
if [ -z "$a" ]; then
	echo "no exported name found in ${cgo[*]}; the probe is reading them wrong"
	exit 1
fi

only_cgo=$(comm -23 <(printf '%s\n' "$a") <(printf '%s\n' "$b"))
only_nocgo=$(comm -13 <(printf '%s\n' "$a") <(printf '%s\n' "$b"))
if [ -z "$only_cgo" ] && [ -z "$only_nocgo" ]; then
	echo "PASS: both builds declare the same $(printf '%s\n' "$a" | wc -l) exported names"
	exit 0
fi
if [ -n "$only_cgo" ]; then
	echo "declared only with cgo, so a consumer without it fails to compile:"
	printf '%s\n' "$only_cgo" | sed 's/^/  /'
fi
if [ -n "$only_nocgo" ]; then
	echo "declared only without cgo:"
	printf '%s\n' "$only_nocgo" | sed 's/^/  /'
fi
exit 1
