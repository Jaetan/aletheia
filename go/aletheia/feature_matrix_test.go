// SPDX-FileCopyrightText: 2025 Nicolas Pelletier
// SPDX-License-Identifier: BSD-2-Clause

// The Go side of the feature-matrix parity gate. It reads
// docs/FEATURE_MATRIX.yaml, which is authoritative, and holds four things:
// every row has an id, a name, a description and one of the three statuses
// for each of the four bindings; an implemented binding names an entry; a
// binding that does not apply gives a reason, so the escape hatch stays
// honest; and every id is distinct. Then every Go entry marked implemented is
// resolved against the package's own declarations, parsed from source, which
// is what catches a public symbol quietly removed or renamed.
//
// A failure means the Go surface and the matrix disagree: put the symbol
// back, or mark the feature planned or not applicable with its reason. The
// Python and C++ parity tests hold their own columns the same way.

package aletheia

import (
	"go/ast"
	"go/parser"
	"go/token"
	"os"
	"path/filepath"
	"strings"
	"testing"

	"gopkg.in/yaml.v3"
)

type featureBinding struct {
	Status string `yaml:"status"`
	Entry  string `yaml:"entry"`
	Reason string `yaml:"reason"`
	Notes  string `yaml:"notes"`
}

type featureBindings struct {
	Python featureBinding `yaml:"python"`
	Cpp    featureBinding `yaml:"cpp"`
	Go     featureBinding `yaml:"go"`
	Rust   featureBinding `yaml:"rust"`
}

type feature struct {
	ID          string          `yaml:"id"`
	Name        string          `yaml:"name"`
	Description string          `yaml:"description"`
	Related     string          `yaml:"related"`
	Bindings    featureBindings `yaml:"bindings"`
}

type featureMatrix struct {
	Features []feature `yaml:"features"`
}

// byBinding is the row's four columns under the names the matrix gives them.
func (b featureBindings) byBinding() map[string]featureBinding {
	return map[string]featureBinding{"python": b.Python, "cpp": b.Cpp, "go": b.Go, "rust": b.Rust}
}

var validParityStatuses = map[string]struct{}{
	"implemented":    {},
	"not_applicable": {},
	"planned":        {},
}

// loadFeatureMatrix reads the matrix, which sits two directories up from the
// package this test runs in.
func loadFeatureMatrix(t *testing.T) featureMatrix {
	t.Helper()
	cwd, err := os.Getwd()
	if err != nil {
		t.Fatalf("getwd: %v", err)
	}
	path := filepath.Join(cwd, "..", "..", "docs", "FEATURE_MATRIX.yaml")
	data, err := os.ReadFile(path)
	if err != nil {
		t.Fatalf("read %s: %v", path, err)
	}
	var m featureMatrix
	if err := yaml.Unmarshal(data, &m); err != nil {
		t.Fatalf("unmarshal %s: %v", path, err)
	}
	if len(m.Features) == 0 {
		t.Fatalf("feature matrix %s has no features", path)
	}
	return m
}

// Every row is complete, every column carries a valid status with the field
// that status requires, and no id appears twice.
func TestFeatureMatrixSchema(t *testing.T) {
	matrix := loadFeatureMatrix(t)
	seen := make(map[string]bool, len(matrix.Features))
	for _, f := range matrix.Features {
		if strings.TrimSpace(f.ID) == "" {
			t.Errorf("a feature has an empty id: %+v", f)
			continue
		}
		if seen[f.ID] {
			t.Errorf("feature id %q appears twice", f.ID)
		}
		seen[f.ID] = true
		t.Run(f.ID, func(t *testing.T) {
			if strings.TrimSpace(f.Name) == "" {
				t.Errorf("%s: no name", f.ID)
			}
			if strings.TrimSpace(f.Description) == "" {
				t.Errorf("%s: no description", f.ID)
			}
			for name, b := range f.Bindings.byBinding() {
				if _, ok := validParityStatuses[b.Status]; !ok {
					t.Errorf("%s.%s: status %q is not implemented, not_applicable or planned", f.ID, name, b.Status)
				}
				if b.Status == "implemented" && strings.TrimSpace(b.Entry) == "" {
					t.Errorf("%s.%s: an implemented binding must name its entry", f.ID, name)
				}
				if b.Status == "not_applicable" && strings.TrimSpace(b.Reason) == "" {
					t.Errorf("%s.%s: a binding that does not apply must give its reason", f.ID, name)
				}
			}
		})
	}
}

// collectGoSymbols parses the package's non-test sources and returns the
// names they declare: functions, types, constants and variables by their own
// name, methods as ReceiverType.Method.
func collectGoSymbols(t *testing.T, pkgDir string) map[string]struct{} {
	t.Helper()
	entries, err := os.ReadDir(pkgDir)
	if err != nil {
		t.Fatalf("readdir %s: %v", pkgDir, err)
	}
	fset := token.NewFileSet()
	syms := make(map[string]struct{})
	for _, e := range entries {
		name := e.Name()
		if e.IsDir() || !strings.HasSuffix(name, ".go") || strings.HasSuffix(name, "_test.go") {
			continue
		}
		path := filepath.Join(pkgDir, name)
		file, err := parser.ParseFile(fset, path, nil, parser.SkipObjectResolution)
		if err != nil {
			t.Fatalf("parse %s: %v", path, err)
		}
		for _, decl := range file.Decls {
			switch d := decl.(type) {
			case *ast.FuncDecl:
				if d.Recv != nil && len(d.Recv.List) > 0 {
					if recv := receiverTypeName(d.Recv.List[0].Type); recv != "" {
						syms[recv+"."+d.Name.Name] = struct{}{}
					}
					continue
				}
				syms[d.Name.Name] = struct{}{}
			case *ast.GenDecl:
				for _, spec := range d.Specs {
					switch s := spec.(type) {
					case *ast.TypeSpec:
						syms[s.Name.Name] = struct{}{}
					case *ast.ValueSpec:
						for _, ident := range s.Names {
							syms[ident.Name] = struct{}{}
						}
					}
				}
			}
		}
	}
	return syms
}

// receiverTypeName is the name behind a receiver written as T, *T or T[X],
// and empty for anything else.
func receiverTypeName(expr ast.Expr) string {
	switch t := expr.(type) {
	case *ast.Ident:
		return t.Name
	case *ast.StarExpr:
		return receiverTypeName(t.X)
	case *ast.IndexExpr:
		return receiverTypeName(t.X)
	default:
		return ""
	}
}

// Every Go entry marked implemented names something the package declares, or,
// when written as "package:Symbol", something the named sibling package
// declares.
func TestFeatureMatrixGoEntriesResolve(t *testing.T) {
	matrix := loadFeatureMatrix(t)
	cwd, err := os.Getwd()
	if err != nil {
		t.Fatalf("getwd: %v", err)
	}
	mainSyms := collectGoSymbols(t, cwd)
	subPkgSyms := map[string]map[string]struct{}{}

	for _, f := range matrix.Features {
		if f.Bindings.Go.Status != "implemented" {
			continue
		}
		t.Run(f.ID, func(t *testing.T) {
			entry := strings.TrimSpace(f.Bindings.Go.Entry)
			if entry == "" {
				t.Fatalf("%s: the go entry is empty though the status is implemented", f.ID)
			}
			pkg, sym, inSubPkg := strings.Cut(entry, ":")
			if !inSubPkg {
				if _, ok := mainSyms[entry]; !ok {
					t.Errorf("%s: the go entry %q is not declared in the aletheia package", f.ID, entry)
				}
				return
			}
			syms, ok := subPkgSyms[pkg]
			if !ok {
				subDir := filepath.Join(cwd, "..", pkg)
				if _, err := os.Stat(subDir); err != nil {
					t.Fatalf("%s: the go sub-package %q is not at %s", f.ID, pkg, subDir)
				}
				syms = collectGoSymbols(t, subDir)
				subPkgSyms[pkg] = syms
			}
			if _, ok := syms[sym]; !ok {
				t.Errorf("%s: the go entry %q names %q, which the %q package does not declare", f.ID, entry, sym, pkg)
			}
		})
	}
}
