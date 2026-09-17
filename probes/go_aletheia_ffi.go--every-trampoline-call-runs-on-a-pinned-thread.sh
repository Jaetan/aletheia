#!/usr/bin/env bash
# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
#
# Probes go/aletheia/ffi.go.
# Claim: every function that calls a C trampoline (a `C.call_*` function, the
# only way the backend reaches the loaded library) pins its goroutine to an
# OS thread first with runtime.LockOSThread, because the GHC RTS keeps
# per-capability state and dlerror is thread-local. The check is syntactic,
# over the file's own AST, so a new method that calls a trampoline without the
# pin is caught without running anything. Non-zero exit: a function calls a
# trampoline and never pins, or ffi.go no longer parses. Exits 2 without Go.
set -u
cd "$(dirname "$0")/.." || exit 2
command -v go > /dev/null || exit 2
scratch=$(mktemp -d)
trap 'rm -rf "$scratch"' EXIT
cat > "$scratch/main.go" <<'GO'
package main

import (
	"fmt"
	"go/ast"
	"go/parser"
	"go/token"
	"os"
	"strings"
)

func main() {
	fset := token.NewFileSet()
	file, err := parser.ParseFile(fset, os.Getenv("PROBED_FILE"), nil, 0)
	if err != nil {
		fmt.Println("ffi.go does not parse:", err)
		os.Exit(2)
	}
	bad := 0
	seen := 0
	for _, decl := range file.Decls {
		fn, ok := decl.(*ast.FuncDecl)
		if !ok || fn.Body == nil {
			continue
		}
		callsTrampoline, pins := false, false
		ast.Inspect(fn.Body, func(n ast.Node) bool {
			sel, ok := n.(*ast.SelectorExpr)
			if !ok {
				return true
			}
			pkg, ok := sel.X.(*ast.Ident)
			if !ok {
				return true
			}
			if pkg.Name == "C" && strings.HasPrefix(sel.Sel.Name, "call_") {
				callsTrampoline = true
			}
			if pkg.Name == "runtime" && sel.Sel.Name == "LockOSThread" {
				pins = true
			}
			return true
		})
		if callsTrampoline {
			seen++
			if !pins {
				bad++
				fmt.Printf("%s calls a trampoline without pinning (line %d)\n", fn.Name.Name, fset.Position(fn.Pos()).Line)
			}
		}
	}
	if seen == 0 {
		fmt.Println("no function calls a trampoline; the claim is untestable")
		os.Exit(1)
	}
	if bad > 0 {
		os.Exit(1)
	}
	fmt.Printf("PASS: all %d trampoline-calling functions pin their thread\n", seen)
}
GO
PROBED_FILE="$PWD/go/aletheia/ffi.go" GOWORK=off go run "$scratch/main.go"
