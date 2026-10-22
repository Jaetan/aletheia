// SPDX-FileCopyrightText: 2025 Nicolas Pelletier
// SPDX-License-Identifier: BSD-2-Clause

// The doc-example harness's check of the errors a fence throws away. The
// forwarding stand-in kernel sees only the kernel's refusals; a binding
// refuses some inputs itself (an identifier out of range, a DLC above 15),
// and a fence that assigns such an error to the blank identifier, declares
// it and never reads it, or calls a function returning it as a statement or
// in a defer, would pass on its exit status. The harness hands each such
// value to docExampleDiscarded, which ends the run on an error. The rewrite
// needs no kernel, so it builds without cgo.

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

// fragmentHead and fragmentTail make a body fragment a file go/parser reads.
const (
	fragmentHead = "package x\nfunc f() {\n"
	fragmentTail = "\n}\n"
)

// discardedErrors is the function a wrapped fence hands every value it
// threw away: an error among them ends the run, naming where.
const discardedErrors = `
func docExampleDiscarded(where string, values ...any) {
	for _, value := range values {
		if err, ok := value.(error); ok && err != nil {
			panic("the example discards an error at " + where + ": " + err.Error())
		}
	}
}

func docExampleDiscardedCall(where string) func(...any) {
	return func(values ...any) { docExampleDiscarded(where, values...) }
}
`

// errorReturning is the name of every exported function and method of the
// two Go modules' packages whose last result is an error, read from their
// sources: a fence calling one as a statement throws that error away.
func errorReturning() (map[string]bool, error) {
	names := map[string]bool{}
	for _, dir := range []string{".", filepath.Join("..", "excel")} {
		paths, err := filepath.Glob(filepath.Join(dir, "*.go"))
		if err != nil {
			return nil, err
		}
		for _, path := range paths {
			if strings.HasSuffix(path, "_test.go") {
				continue
			}
			src, err := os.ReadFile(path)
			if err != nil {
				return nil, err
			}
			file, err := parser.ParseFile(token.NewFileSet(), path, src, 0)
			if err != nil {
				return nil, err
			}
			for _, decl := range file.Decls {
				fn, ok := decl.(*ast.FuncDecl)
				if !ok || !fn.Name.IsExported() || fn.Type.Results == nil {
					continue
				}
				results := fn.Type.Results.List
				if last, ok := results[len(results)-1].Type.(*ast.Ident); ok && last.Name == "error" {
					names[fn.Name.Name] = true
				}
			}
		}
	}
	return names, nil
}

// calledName is the name a call statement calls, a function's or a method's.
func calledName(expr ast.Expr) string {
	call, ok := expr.(*ast.CallExpr)
	if !ok {
		return ""
	}
	switch fun := call.Fun.(type) {
	case *ast.Ident:
		return fun.Name
	case *ast.SelectorExpr:
		return fun.Sel.Name
	}
	return ""
}

// discardSite names the document line of a statement on line of a file whose
// first lines are head, the fence opening at line opening of doc.
func discardSite(doc string, opening, line int, head string) string {
	return fmt.Sprintf("%s:L%d", doc, opening+line-strings.Count(head, "\n"))
}

// statementLists are the statement lists a node holds: a block's, and a
// switch or select clause's.
func statementLists(node ast.Node) []ast.Stmt {
	switch n := node.(type) {
	case *ast.BlockStmt:
		return n.List
	case *ast.CaseClause:
		return n.Body
	case *ast.CommClause:
		return n.Body
	}
	return nil
}

// rewriteDiscards returns src with each blank on the left of an assignment
// in a statement list replaced by a variable the assignment fills, declared
// before it, and the assignment followed by a call handing those variables
// to docExampleDiscarded; and with each call statement, plain or deferred,
// of a function errorFuncs names handing its results to the same check.
// head and tail are what makes src a file go/parser reads; a src that does
// not parse comes back as it was, for the build to report.
func rewriteDiscards(src, head, tail, doc string, opening int, errorFuncs map[string]bool) string {
	fset := token.NewFileSet()
	file, err := parser.ParseFile(fset, "", head+src+tail, 0)
	if err != nil {
		return src
	}
	type edit struct {
		at, drop int
		text     string
	}
	var edits []edit
	held := 0
	ast.Inspect(file, func(node ast.Node) bool {
		for _, stmt := range statementLists(node) {
			var call ast.Expr
			switch s := stmt.(type) {
			case *ast.ExprStmt:
				call = s.X
			case *ast.DeferStmt:
				call = s.Call
			}
			if call != nil && errorFuncs[calledName(call)] {
				where := discardSite(doc, opening, fset.Position(stmt.Pos()).Line, head)
				open, shut := fmt.Sprintf("docExampleDiscardedCall(%q)(", where), ")"
				if _, deferred := stmt.(*ast.DeferStmt); deferred {
					open, shut = "func() { "+open, shut+" }()"
				}
				edits = append(edits,
					edit{fset.Position(call.Pos()).Offset - len(head), 0, open},
					edit{fset.Position(call.End()).Offset - len(head), 0, shut})
				continue
			}
			assign, ok := stmt.(*ast.AssignStmt)
			if !ok {
				continue
			}
			var names []string
			for _, lhs := range assign.Lhs {
				if id, ok := lhs.(*ast.Ident); ok && id.Name == "_" {
					held++
					name := fmt.Sprintf("docDiscard%d", held)
					names = append(names, name)
					edits = append(edits, edit{fset.Position(id.Pos()).Offset - len(head), 1, name})
				}
			}
			if len(names) == 0 {
				continue
			}
			start := fset.Position(assign.Pos())
			list := strings.Join(names, ", ")
			where := discardSite(doc, opening, start.Line, head)
			edits = append(edits,
				edit{start.Offset - len(head), 0, "var " + list + " any; "},
				edit{fset.Position(assign.End()).Offset - len(head), 0, fmt.Sprintf("; docExampleDiscarded(%q, %s)", where, list)})
		}
		return true
	})
	// From the end, a replacement before an insertion at the same offset.
	slices.SortFunc(edits, func(a, b edit) int {
		if a.at != b.at {
			return b.at - a.at
		}
		return b.drop - a.drop
	})
	out := src
	for _, e := range edits {
		out = out[:e.at] + e.text + out[e.at+e.drop:]
	}
	return out
}

func TestRewriteDiscardsHandsEveryDiscardedErrorToTheCheck(t *testing.T) {
	for _, tc := range []struct{ name, src, want string }{
		{
			"a defined pair",
			"id, _ := aletheia.NewStandardID(0x100)",
			`var docDiscard1 any; id, docDiscard1 := aletheia.NewStandardID(0x100); docExampleDiscarded("d.md:L11", docDiscard1)`,
		},
		{
			"an assigned tuple",
			"_, _ = checks, err",
			`var docDiscard1, docDiscard2 any; docDiscard1, docDiscard2 = checks, err; docExampleDiscarded("d.md:L11", docDiscard1, docDiscard2)`,
		},
		{
			"a switch clause, on its own line",
			"x := 1\nswitch x {\ncase 1:\n\t_ = f()\n}",
			"x := 1\nswitch x {\ncase 1:\n\t" + `var docDiscard1 any; docDiscard1 = f(); docExampleDiscarded("d.md:L14", docDiscard1)` + "\n}",
		},
		{"no blank", "x := f()", "x := f()"},
		{"a range's blank", "for _, v := range xs {\n\tuse(v)\n}", "for _, v := range xs {\n\tuse(v)\n}"},
		{"a fragment that does not parse", "_ = (", "_ = ("},
		{
			"a call statement returning an error",
			"client.Close()",
			`docExampleDiscardedCall("d.md:L11")(client.Close())`,
		},
		{
			"a deferred one",
			"defer client.Close()",
			`defer func() { docExampleDiscardedCall("d.md:L11")(client.Close()) }()`,
		},
		{"a call statement returning no error", "fmt.Println(x)", "fmt.Println(x)"},
	} {
		t.Run(tc.name, func(t *testing.T) {
			got := rewriteDiscards(tc.src, fragmentHead, fragmentTail, "d.md", 10, map[string]bool{"Close": true})
			if got != tc.want {
				t.Errorf("rewriteDiscards(%q)\n got %q\nwant %q", tc.src, got, tc.want)
			}
		})
	}
}

func TestErrorReturningReadsTheBindingsSources(t *testing.T) {
	names, err := errorReturning()
	if err != nil {
		t.Fatalf("read the bindings' sources: %v", err)
	}
	for _, name := range []string{"Close", "ParseDBC", "LoadChecks", "NewStandardID"} {
		if !names[name] {
			t.Errorf("%s returns an error and is not in the set", name)
		}
	}
	if names["NeverExceeds"] {
		t.Error("NeverExceeds cannot fail and is in the set")
	}
}
