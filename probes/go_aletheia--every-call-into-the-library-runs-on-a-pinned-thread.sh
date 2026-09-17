#!/usr/bin/env bash
# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
#
# Probes go/aletheia/ffi.go, go/aletheia/renderer.go and go/aletheia/decimal.go.
# Claim: every call into the loaded library, from any of the three files that
# make one, happens on a goroutine pinned to an OS thread, because the GHC
# runtime keeps state per capability and dlerror is thread-local. A call is
# either through a C trampoline, which is how a session reaches the library, or
# through the dynamic loader itself, which is how the two consumers outside a
# session find their symbols. A function satisfies this by calling runtime.LockOSThread
# itself, or by being called only from functions that satisfy it, which is how
# a shared helper is covered. A helper with no caller in the file satisfies
# nothing. The check is syntactic, over the file own AST and its call graph, so
# a new method that calls a trampoline without the pin is caught without
# running anything. Non-zero exit: a trampoline can be reached unpinned, two
# functions share a name, which would make the call graph unsound, or ffi.go no
# longer parses. Exits 2 without Go.
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
	"sort"
	"strings"
)

// reachesLibrary reports whether a C name is a call into the loaded library:
// a trampoline, which every file names for itself, or the dynamic loader,
// whose error is the thread-local one the pin is for.
func reachesLibrary(name string) bool {
	for _, prefix := range []string{"call_", "renderer_call_", "decimal_call_"} {
		if strings.HasPrefix(name, prefix) {
			return true
		}
	}
	switch name {
	case "dlopen", "dlsym", "dlerror", "dlclose":
		return true
	}
	return false
}

type fnInfo struct {
	line    int
	pins    bool
	direct  bool
	callers map[string]struct{}
}

func main() {
	fset := token.NewFileSet()
	path := os.Getenv("PROBED_FILE")
	file, err := parser.ParseFile(fset, path, nil, 0)
	if err != nil {
		fmt.Println(path, "does not parse:", err)
		os.Exit(2)
	}

	fns := map[string]*fnInfo{}
	var order []string
	for _, decl := range file.Decls {
		fn, ok := decl.(*ast.FuncDecl)
		if !ok || fn.Body == nil {
			continue
		}
		if _, dup := fns[fn.Name.Name]; dup {
			fmt.Printf("two functions are named %s; the call graph would be unsound\n", fn.Name.Name)
			os.Exit(1)
		}
		fns[fn.Name.Name] = &fnInfo{line: fset.Position(fn.Pos()).Line, callers: map[string]struct{}{}}
		order = append(order, fn.Name.Name)
	}

	// Second pass, now that every name is known: who pins, who reaches a
	// trampoline directly, and who calls whom.
	for _, decl := range file.Decls {
		fn, ok := decl.(*ast.FuncDecl)
		if !ok || fn.Body == nil {
			continue
		}
		self := fns[fn.Name.Name]
		ast.Inspect(fn.Body, func(n ast.Node) bool {
			switch node := n.(type) {
			case *ast.SelectorExpr:
				pkg, ok := node.X.(*ast.Ident)
				if !ok {
					return true
				}
				if pkg.Name == "C" && reachesLibrary(node.Sel.Name) {
					self.direct = true
				}
				if pkg.Name == "runtime" && node.Sel.Name == "LockOSThread" {
					self.pins = true
				}
			case *ast.CallExpr:
				name := ""
				switch callee := node.Fun.(type) {
				case *ast.Ident:
					name = callee.Name
				case *ast.SelectorExpr:
					name = callee.Sel.Name
				}
				if callee, ok := fns[name]; ok && name != fn.Name.Name {
					callee.callers[fn.Name.Name] = struct{}{}
				}
			}
			return true
		})
	}

	// A function runs pinned when it pins, or when it has callers and every
	// one of them runs pinned. A cycle without a pin in it runs unpinned.
	const (
		unknown = iota
		visiting
		yes
		no
	)
	state := map[string]int{}
	var pinned func(string) bool
	pinned = func(name string) bool {
		switch state[name] {
		case yes:
			return true
		case no, visiting:
			return false
		}
		fn := fns[name]
		if fn.pins {
			state[name] = yes
			return true
		}
		state[name] = visiting
		ok := len(fn.callers) > 0
		for caller := range fn.callers {
			if !pinned(caller) {
				ok = false
				break
			}
		}
		if ok {
			state[name] = yes
		} else {
			state[name] = no
		}
		return ok
	}

	bad, seen := 0, 0
	for _, name := range order {
		if !fns[name].direct {
			continue
		}
		seen++
		if pinned(name) {
			continue
		}
		bad++
		callers := make([]string, 0, len(fns[name].callers))
		for c := range fns[name].callers {
			callers = append(callers, c)
		}
		sort.Strings(callers)
		where := "no caller in the file"
		if len(callers) > 0 {
			where = "called from " + strings.Join(callers, ", ")
		}
		fmt.Printf("%s reaches the library unpinned (line %d, %s)\n", name, fns[name].line, where)
	}
	if seen == 0 {
		fmt.Println(path, "reaches the library nowhere; the claim is untestable there")
		os.Exit(1)
	}
	if bad > 0 {
		os.Exit(1)
	}
	shape := fmt.Sprintf("all %d functions that reach the library run pinned", seen)
	if seen == 1 {
		shape = "the one function that reaches the library runs pinned"
	}
	fmt.Printf("%s: %s\n", path, shape)
}
GO
status=0
for f in ffi.go renderer.go decimal.go; do
	PROBED_FILE="$PWD/go/aletheia/$f" GOWORK=off go run "$scratch/main.go" || status=1
done
[ "$status" -eq 0 ] || exit 1
echo "PASS: every call into the library, in all three files, runs pinned"
