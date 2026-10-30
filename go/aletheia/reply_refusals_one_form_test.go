// SPDX-FileCopyrightText: 2025 Nicolas Pelletier
// SPDX-License-Identifier: BSD-2-Clause

// Every refusal of a reply place is built by replyRefusal, which writes the
// one form. A protocol error the package builds anywhere else is one the form
// leaves alone: the kernel's own message carried with its code, the binary
// extraction reply's layout, a library that answered no reply at all, or a
// command of the package's own its encoder could not write. Each such site is
// listed with its count, so a protocol error built by hand anywhere else is
// red, and so is a listed site that no longer builds one.

package aletheia_test

import (
	"fmt"
	"go/ast"
	"go/parser"
	"go/token"
	"os"
	"path/filepath"
	"slices"
	"strings"
	"testing"
)

// protocolSite is a function of the package building a protocol error itself:
// its file, and its name, a method's led by its receiver type.
type protocolSite struct {
	file     string
	function string
}

// leftAlone is what each function outside the one form builds by hand, and
// why the form leaves it alone.
var leftAlone = map[protocolSite]int{
	// The one form itself.
	{"reply_shape.go", "replyRefusal"}: 1,
	// The constructors every other site calls.
	{"error.go", "protocolError"}:     1,
	{"error.go", "wrapProtocolError"}: 1,
	// The kernel's own message, carried with its code.
	{"json_response.go", "checkErrorStatus"}: 1,
	// The binary extraction reply's layout, which the reply proof does not reach.
	{"json_response.go", "parseExtractionBin"}: 6,
	// A library that answered no reply: an entry refusing without its envelope.
	{"decimal.go", "FromDecimal"}:              1,
	{"ffi.go", "FFIBackend.binaryStatusError"}: 1,
	{"property_check.go", "entryRefusal"}:      1,
	// A command or a definition of the package's own its encoder could not write.
	{"json.go", "serializeCommand"}: 1,
	{"json.go", "serializeDBC"}:     1,
}

// protocolErrorsBuilt counts each function's protocol errors across the
// package's non-test files: a call to protocolError or wrapProtocolError, a
// call handed ErrProtocol, and an Error literal whose Kind is ErrProtocol.
// The source is read whatever its build constraints say.
func protocolErrorsBuilt(t *testing.T) map[protocolSite]int {
	t.Helper()
	paths, err := filepath.Glob("*.go")
	if err != nil {
		t.Fatalf("listing the package's files: %v", err)
	}
	fset := token.NewFileSet()
	built := map[protocolSite]int{}
	for _, path := range paths {
		if strings.HasSuffix(path, "_test.go") {
			continue
		}
		src, err := os.ReadFile(path)
		if err != nil {
			t.Fatalf("reading %s: %v", path, err)
		}
		file, err := parser.ParseFile(fset, path, src, parser.SkipObjectResolution)
		if err != nil {
			t.Fatalf("parsing %s: %v", path, err)
		}
		for _, decl := range file.Decls {
			site := protocolSite{file: path, function: "<package level>"}
			if fn, ok := decl.(*ast.FuncDecl); ok {
				site.function = functionName(fn)
			}
			ast.Inspect(decl, func(n ast.Node) bool {
				if buildsProtocolError(n) {
					built[site]++
				}
				return true
			})
		}
	}
	return built
}

// functionName is a function's name, a method's led by its receiver type.
func functionName(fn *ast.FuncDecl) string {
	if fn.Recv == nil || len(fn.Recv.List) == 0 {
		return fn.Name.Name
	}
	recv := fn.Recv.List[0].Type
	if star, ok := recv.(*ast.StarExpr); ok {
		recv = star.X
	}
	switch generic := recv.(type) {
	case *ast.IndexExpr:
		recv = generic.X
	case *ast.IndexListExpr:
		recv = generic.X
	}
	if id, ok := recv.(*ast.Ident); ok {
		return id.Name + "." + fn.Name.Name
	}
	return fn.Name.Name
}

// isIdent holds when e is the bare identifier name.
func isIdent(e ast.Expr, name string) bool {
	id, ok := e.(*ast.Ident)
	return ok && id.Name == name
}

// buildsProtocolError holds when n builds an error of kind ErrProtocol.
func buildsProtocolError(n ast.Node) bool {
	switch n := n.(type) {
	case *ast.CallExpr:
		if isIdent(n.Fun, "protocolError") || isIdent(n.Fun, "wrapProtocolError") {
			return true
		}
		return slices.ContainsFunc(n.Args, func(arg ast.Expr) bool { return isIdent(arg, "ErrProtocol") })
	case *ast.CompositeLit:
		return slices.ContainsFunc(n.Elts, func(elt ast.Expr) bool {
			kv, ok := elt.(*ast.KeyValueExpr)
			return ok && isIdent(kv.Key, "Kind") && isIdent(kv.Value, "ErrProtocol")
		})
	}
	return false
}

// No function builds a protocol error itself but those the form leaves alone.
func TestEveryRefusalOfAReplyPlaceIsBuiltByTheOneForm(t *testing.T) {
	built := protocolErrorsBuilt(t)
	var unlisted, moved []string
	for site, n := range built {
		if _, listed := leftAlone[site]; !listed {
			unlisted = append(unlisted, fmt.Sprintf("%s:%s x%d", site.file, site.function, n))
		}
	}
	for site, n := range leftAlone {
		if built[site] != n {
			moved = append(moved, fmt.Sprintf("%s:%s lists %d, builds %d", site.file, site.function, n, built[site]))
		}
	}
	slices.Sort(unlisted)
	slices.Sort(moved)
	if len(unlisted) != 0 || len(moved) != 0 {
		t.Errorf("protocol errors built outside the one form:\nunlisted: %q\nmoved: %q", unlisted, moved)
	}
}
