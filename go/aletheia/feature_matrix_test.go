// Feature matrix parity test — Go side.
//
// Reads docs/FEATURE_MATRIX.yaml and verifies:
//
//  1. Every feature row has a well-formed schema (id / name / description /
//     bindings for all three languages, each with a valid status).
//  2. Every binding with status=implemented carries an entry field.
//  3. Every Go implemented entry resolves via go/ast source parsing —
//     catches silent removal or rename of a public symbol.
//  4. Every binding with status=not_applicable carries a non-empty reason.
//
// Failure here means the Go public surface drifted from what the matrix
// declares. Fix: either the code (add the symbol back), or the matrix
// (mark the feature as planned or not_applicable with justification).
//
// See docs/development/PARITY_PLAN.md for the rationale and roadmap.

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

var validParityStatuses = map[string]struct{}{
	"implemented":    {},
	"not_applicable": {},
	"planned":        {},
}

// loadFeatureMatrix reads and parses docs/FEATURE_MATRIX.yaml located two
// directories up from the test working directory (go/aletheia/ → repo root).
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

// TestFeatureMatrixSchema validates per-row schema integrity for all three
// bindings. The same shape is enforced in the Python and C++ parity tests.
func TestFeatureMatrixSchema(t *testing.T) {
	matrix := loadFeatureMatrix(t)
	for _, f := range matrix.Features {
		f := f
		t.Run(f.ID, func(t *testing.T) {
			if strings.TrimSpace(f.ID) == "" {
				t.Errorf("feature has empty id")
			}
			if strings.TrimSpace(f.Name) == "" {
				t.Errorf("%s: missing name", f.ID)
			}
			if strings.TrimSpace(f.Description) == "" {
				t.Errorf("%s: missing description", f.ID)
			}
			checkBinding(t, f.ID, "python", f.Bindings.Python)
			checkBinding(t, f.ID, "cpp", f.Bindings.Cpp)
			checkBinding(t, f.ID, "go", f.Bindings.Go)
		})
	}
}

func checkBinding(t *testing.T, fid, name string, b featureBinding) {
	t.Helper()
	if _, ok := validParityStatuses[b.Status]; !ok {
		t.Errorf("%s.%s: invalid status %q (want implemented|not_applicable|planned)", fid, name, b.Status)
	}
	if b.Status == "implemented" && strings.TrimSpace(b.Entry) == "" {
		t.Errorf("%s.%s: status=implemented requires non-empty entry", fid, name)
	}
	if b.Status == "not_applicable" && strings.TrimSpace(b.Reason) == "" {
		t.Errorf("%s.%s: status=not_applicable requires non-empty reason — the escape hatch must stay honest", fid, name)
	}
}

// collectGoSymbols parses all non-test .go files in pkgDir and returns a set
// of declared identifiers. Top-level func / type / const / var names are
// stored bare; methods are stored as "ReceiverType.Method" (receiver is
// unwrapped through pointer and generic index expressions).
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
				} else {
					syms[d.Name.Name] = struct{}{}
				}
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

// receiverTypeName unwraps *T, T, and T[X] receiver shapes and returns the
// underlying type name, or "" if the expression is not a simple identifier.
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

// TestFeatureMatrixGoEntriesResolve verifies every Go implemented entry
// resolves to a declared symbol in the aletheia package (or a named
// sub-package like "excel"). Catches silent removal or rename.
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
		f := f
		t.Run(f.ID, func(t *testing.T) {
			entry := strings.TrimSpace(f.Bindings.Go.Entry)
			if entry == "" {
				t.Fatalf("%s: go entry is empty despite status=implemented", f.ID)
			}

			if idx := strings.IndexByte(entry, ':'); idx > 0 {
				pkg := entry[:idx]
				sym := entry[idx+1:]
				syms, ok := subPkgSyms[pkg]
				if !ok {
					subDir := filepath.Join(cwd, "..", pkg)
					if _, err := os.Stat(subDir); err != nil {
						t.Fatalf("%s: go sub-package %q not found at %s", f.ID, pkg, subDir)
					}
					syms = collectGoSymbols(t, subDir)
					subPkgSyms[pkg] = syms
				}
				if _, ok := syms[sym]; !ok {
					t.Errorf("%s: go entry %q — symbol %q not declared in sub-package %q", f.ID, entry, sym, pkg)
				}
				return
			}

			if _, ok := mainSyms[entry]; !ok {
				t.Errorf("%s: go entry %q not declared in aletheia package", f.ID, entry)
			}
		})
	}
}
