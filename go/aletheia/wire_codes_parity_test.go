// SPDX-FileCopyrightText: 2025 Nicolas Pelletier
// SPDX-License-Identifier: BSD-2-Clause

// The two code vocabularies this binding carries are the ones
// docs/WIRE_CODES.yaml names, which the orchestrator's own gate anchors to the
// kernel. Go offering no way to enumerate constants, the test reads each
// vocabulary's constants from the package's source and holds them, the set the
// reply readers read its codes from and its section to one set of codes: a
// constant left out of the set and the document fails, and so does a row no
// constant declares.
//
// The Python, C++ and Rust suites hold their own vocabularies against the
// document.

package aletheia_test

import (
	"go/ast"
	"go/constant"
	"go/parser"
	"go/token"
	"maps"
	"os"
	"path/filepath"
	"slices"
	"strings"
	"testing"

	"gopkg.in/yaml.v3"

	"github.com/Jaetan/aletheia/go/v5/aletheia"
)

type wireCodeRow struct {
	Name        string `yaml:"name"`
	Description string `yaml:"description"`
}

type wireCodeDoc struct {
	IssueCodes []wireCodeRow `yaml:"issue_codes"`
	ErrorCodes []wireCodeRow `yaml:"error_codes"`
}

// loadWireCodes reads the document from the repository RepoRoot names.
func loadWireCodes(t *testing.T) wireCodeDoc {
	t.Helper()
	yamlPath := filepath.Join(aletheia.RepoRoot(t), "docs", "WIRE_CODES.yaml")
	data, err := os.ReadFile(yamlPath)
	if err != nil {
		t.Fatalf("read %s: %v", yamlPath, err)
	}
	var doc wireCodeDoc
	if err := yaml.Unmarshal(data, &doc); err != nil {
		t.Fatalf("unmarshal %s: %v", yamlPath, err)
	}
	if len(doc.IssueCodes) == 0 || len(doc.ErrorCodes) == 0 {
		t.Fatalf("%s: empty issue_codes or error_codes section", yamlPath)
	}
	return doc
}

// yamlNameSet collects one section's names, failing on empties or duplicates.
func yamlNameSet(t *testing.T, section string, rows []wireCodeRow) map[string]struct{} {
	t.Helper()
	names := make(map[string]struct{}, len(rows))
	for i, row := range rows {
		if row.Name == "" {
			t.Fatalf("%s[%d]: empty name", section, i)
		}
		if _, dup := names[row.Name]; dup {
			t.Fatalf("%s[%d]: duplicate name %q", section, i, row.Name)
		}
		names[row.Name] = struct{}{}
	}
	return names
}

// Every row of both sections names a code once and says what it is for.
func TestWireCodesYAMLSchema(t *testing.T) {
	doc := loadWireCodes(t)
	for section, rows := range map[string][]wireCodeRow{
		"issue_codes": doc.IssueCodes,
		"error_codes": doc.ErrorCodes,
	} {
		yamlNameSet(t, section, rows) // non-empty + unique names
		for i, row := range rows {
			if row.Description == "" {
				t.Errorf("%s[%d] (%s): missing description", section, i, row.Name)
			}
		}
	}
}

// Each vocabulary's constants, its readers' set and its section name the same
// codes.
func TestWireCodes_MatchTheirSections(t *testing.T) {
	doc := loadWireCodes(t)
	declared := declaredCodes(t)
	cases := map[string]struct {
		rows     []wireCodeRow
		declared map[string]struct{}
		read     map[string]struct{}
	}{
		"issue codes": {doc.IssueCodes, declared["IssueCode"], codeWords(aletheia.IssueCodes)},
		"error codes": {doc.ErrorCodes, declared["ErrorCode"], codeWords(aletheia.ErrorCodes)},
	}
	for section, tc := range cases {
		t.Run(section, func(t *testing.T) {
			holders := []struct {
				name  string
				codes map[string]struct{}
			}{
				{"the package's constants", tc.declared},
				{"the readers' set", tc.read},
				{"the document", yamlNameSet(t, section, tc.rows)},
			}
			every := map[string]struct{}{}
			for _, holder := range holders {
				maps.Copy(every, holder.codes)
			}
			for _, code := range slices.Sorted(maps.Keys(every)) {
				var lacking []string
				for _, holder := range holders {
					if _, ok := holder.codes[code]; !ok {
						lacking = append(lacking, holder.name)
					}
				}
				if len(lacking) > 0 {
					t.Errorf("%s: %q is not in %s", section, code, strings.Join(lacking, " or "))
				}
			}
		})
	}
}

// declaredCodes reads the package's non-test files, whatever their build
// constraints say, for the constants declared with each code type, by the
// type's name.
func declaredCodes(t *testing.T) map[string]map[string]struct{} {
	t.Helper()
	paths, err := filepath.Glob("*.go")
	if err != nil {
		t.Fatalf("listing the package's files: %v", err)
	}
	declared := map[string]map[string]struct{}{"ErrorCode": {}, "IssueCode": {}}
	fset := token.NewFileSet()
	for _, path := range paths {
		if strings.HasSuffix(path, "_test.go") {
			continue
		}
		file, err := parser.ParseFile(fset, path, nil, parser.SkipObjectResolution)
		if err != nil {
			t.Fatalf("parsing %s: %v", path, err)
		}
		for _, decl := range file.Decls {
			gen, ok := decl.(*ast.GenDecl)
			if !ok || gen.Tok != token.CONST {
				continue
			}
			for _, spec := range gen.Specs {
				value := spec.(*ast.ValueSpec)
				typ, ok := value.Type.(*ast.Ident)
				if !ok {
					continue
				}
				codes, ok := declared[typ.Name]
				if !ok {
					continue
				}
				for _, v := range value.Values {
					lit, ok := v.(*ast.BasicLit)
					if !ok || lit.Kind != token.STRING {
						t.Fatalf("%s: a constant of type %s whose value is no string literal", fset.Position(v.Pos()), typ.Name)
					}
					codes[constant.StringVal(constant.MakeFromLiteral(lit.Value, lit.Kind, 0))] = struct{}{}
				}
			}
		}
	}
	return declared
}

// codeWords is the words of a set of codes.
func codeWords[T ~string](codes map[T]struct{}) map[string]struct{} {
	words := make(map[string]struct{}, len(codes))
	for code := range codes {
		words[string(code)] = struct{}{}
	}
	return words
}
