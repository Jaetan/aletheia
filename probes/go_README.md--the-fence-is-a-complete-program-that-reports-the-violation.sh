#!/usr/bin/env bash
# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
#
# Probes go/README.md.
# Claim: the Go fence in the README is a complete program that builds against
# the local module the same way the doc-example harness builds a fence, runs
# to exit 0 against the built kernel, and prints the violation its own comment
# says the frame produces followed by one end-of-stream verdict. Non-zero
# exit: the fence is not a complete program, does not build, does not run to
# exit 0, or no longer demonstrates what its comments claim. Exits 2 when
# build/libaletheia-ffi.so or the Go toolchain is missing.
set -u
cd "$(dirname "$0")/.." || exit 2
lib=$PWD/build/libaletheia-ffi.so
[ -f "$lib" ] || exit 2
command -v go > /dev/null || exit 2
scratch=$PWD/go/build/probe-scratch/readme-fence
rm -rf "$scratch"
mkdir -p "$scratch" || exit 2
awk '/^```go$/{flag=1; next} /^```$/{flag=0} flag' go/README.md > "$scratch/main.go"
grep -q '^package main' "$scratch/main.go" || { echo "fence is not a complete program"; exit 1; }
grep -q '^func main' "$scratch/main.go" || { echo "fence has no main"; exit 1; }
cat > "$scratch/go.mod" <<EOF
module readme_fence

go 1.24.0

require github.com/aletheia-automotive/aletheia-go/v5 v5.0.0

replace github.com/aletheia-automotive/aletheia-go/v5 => $PWD/go
EOF
# The scratch module sits under go/, inside the workspace, so workspace mode is
# switched off and the replace directive above is what resolves the binding.
(cd "$scratch" && GOWORK=off GOFLAGS=-mod=mod go build -o fence . > compile.log 2>&1) || { tail -5 "$scratch/compile.log"; exit 1; }
out=$(cd "$scratch" && ALETHEIA_LIB=$lib ./fence 2>&1); rc=$?
[ "$rc" -eq 0 ] || { echo "the program exited $rc: $out"; exit 1; }
case $out in *"violation:"*) ;; *) echo "the frame the comment calls a violation produced none: $out"; exit 1 ;; esac
case $out in *"1 verdict(s) at end of stream"*) ;; *) echo "end of stream did not report one verdict: $out"; exit 1 ;; esac
rm -rf "$scratch"
echo "PASS: the README fence builds, runs, reports the violation and one verdict"
