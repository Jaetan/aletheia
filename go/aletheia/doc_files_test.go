// SPDX-FileCopyrightText: 2025 Nicolas Pelletier
// SPDX-License-Identifier: BSD-2-Clause

// The documents the doc-example harness runs, the extractor it reads their Go
// fences with, and the gates around them: a tracked document with a Go fence
// is listed and a listed one is tracked and carries one, the way the Python
// harness's list is held; every fence of a whole-program document declares
// package main; no tracked document hides a Go fence from the extractor
// behind a suffixed info word; the listed files keep a floor of fences; and
// the library packages' comments hold no code, which Example functions hold,
// their cgo preambles, the C source cgo compiles, apart.
// None of it needs the kernel, so it builds without cgo.

package aletheia_test

import (
	"bufio"
	"fmt"
	"go/ast"
	"go/doc/comment"
	goparser "go/parser"
	"go/token"
	"os"
	"os/exec"
	"path/filepath"
	"regexp"
	"slices"
	"strings"
	"testing"
	"unicode/utf8"

	"github.com/Jaetan/aletheia/go/v5/aletheia"
)

// docFiles is every tracked Markdown file carrying a Go fence, relative to the
// repository root. Code no check runs opens with tildes, which the extractor
// does not read.
var docFiles = []string{
	"go/README.md",
	"docs/PITCH.md",
	"docs/architecture/CANCELLATION.md",
	"docs/reference/INTERFACES.md",
	"docs/reference/GO_API.md",
	"docs/development/DISTRIBUTION.md",
	"docs/guides/TUTORIAL.md",
}

// wholeProgramDocs is the listed documents whose fences are each a whole
// program, which a reader builds as it stands.
var wholeProgramDocs = []string{
	"go/README.md",
}

// goFence is one Go fence of a listed file.
type goFence struct {
	file    string   // path relative to the repository root
	line    int      // 1-based line number of the opening ```go
	content string   // body between fences (no surrounding ``` lines)
	refuses []string // the codes the line directly above names, in order
}

// refusesMark is the line directly above a fence that shows refusals, naming
// the codes the kernel answers its calls with, in order.
var refusesMark = regexp.MustCompile(`^<!-- refuses: ([a-z0-9_]+(?: [a-z0-9_]+)*) -->$`)

// statedRefusals is the codes a line names when it is a refusesMark, else none.
func statedRefusals(line string) []string {
	m := refusesMark.FindStringSubmatch(line)
	if m == nil {
		return nil
	}
	return strings.Fields(m[1])
}

func (f goFence) name() string {
	return fmt.Sprintf("%s:L%d", f.file, f.line)
}

// packageName is the name a fence's package clause declares, as the Go parser
// reads it, comments before it included, or "" when the fence opens with
// anything else.
func packageName(body string) string {
	file, err := goparser.ParseFile(token.NewFileSet(), "", body, goparser.PackageClauseOnly)
	if err != nil {
		return ""
	}
	return file.Name.Name
}

// fenceOpening is what a line opens, read by the first word of its info
// string. An info string holding a backtick opens nothing, CommonMark reading
// the line as inline code.
type fenceOpening int

const (
	// notAGoFence is any other line.
	notAGoFence fenceOpening = iota
	// runGoFence is the harness's reading: leading blanks stripped, then a
	// fence whose info string's first word is exactly go.
	runGoFence
	// hiddenGoFence is go followed by ASCII punctuation (go,ignore): a reader
	// still takes the fence for Go, and the harness neither runs nor counts
	// it.
	hiddenGoFence
)

func goFenceOpening(line string) fenceOpening {
	rest, ok := strings.CutPrefix(strings.TrimLeft(line, " \t"), "```go")
	switch {
	case !ok || strings.Contains(rest, "`"):
		return notAGoFence
	case rest == "" || rest[0] == ' ' || rest[0] == '\t':
		return runGoFence
	}
	if next := rest[0]; next >= utf8.RuneSelf || next == '_' ||
		'0' <= next && next <= '9' || 'a' <= next && next <= 'z' || 'A' <= next && next <= 'Z' {
		return notAGoFence
	}
	return hiddenGoFence
}

// extractGoFences returns every Go fence of one file, named relative to the
// repository root: an opening line the harness runs, closed by a line that is
// exactly the fence.
func extractGoFences(t *testing.T, file string) []goFence {
	t.Helper()
	data, err := os.ReadFile(filepath.Join(aletheia.RepoRoot(t), file))
	if err != nil {
		t.Fatalf("read %s: %v", file, err)
	}
	var fences []goFence
	scanner := bufio.NewScanner(strings.NewReader(string(data)))
	scanner.Buffer(make([]byte, 1024*1024), 1024*1024)
	var (
		inFence    bool
		fenceStart int
		fenceBody  strings.Builder
		refuses    []string
		lineno     int
		previous   string
	)
	for scanner.Scan() {
		lineno++
		line := scanner.Text()
		if !inFence {
			if goFenceOpening(line) == runGoFence {
				inFence = true
				fenceStart = lineno
				fenceBody.Reset()
				refuses = statedRefusals(previous)
			}
			previous = line
			continue
		}
		if strings.TrimSpace(line) == "```" {
			fences = append(fences, goFence{
				file:    file,
				line:    fenceStart,
				content: fenceBody.String(),
				refuses: refuses,
			})
			inFence = false
			previous = line
			continue
		}
		fenceBody.WriteString(line)
		fenceBody.WriteByte('\n')
	}
	if err := scanner.Err(); err != nil {
		t.Fatalf("scan %s: %v", file, err)
	}
	if inFence {
		t.Fatalf("%s: unterminated ```go fence opened at line %d", file, fenceStart)
	}
	return fences
}

// trackedMarkdown is every tracked Markdown file, repository-relative, as git
// lists it: the set a fresh checkout holds, so an untracked file in the
// working tree is never read.
func trackedMarkdown(t *testing.T) []string {
	t.Helper()
	out, err := exec.Command("git", "-C", aletheia.RepoRoot(t), "ls-files", "-z", "--", "*.md", "*.mdx", "*.svx").Output()
	if err != nil {
		t.Fatalf("git ls-files: %v", err)
	}
	return strings.FieldsFunc(string(out), func(r rune) bool { return r == 0 })
}

func TestEveryTrackedGoFenceIsInAListedDocument(t *testing.T) {
	var unlisted []string
	for _, doc := range trackedMarkdown(t) {
		if !slices.Contains(docFiles, doc) && len(extractGoFences(t, doc)) > 0 {
			unlisted = append(unlisted, doc)
		}
	}
	if len(unlisted) > 0 {
		t.Errorf("Go fences the harness does not run: %v", unlisted)
	}
}

func TestEveryListedDocumentIsTrackedAndCarriesAGoFence(t *testing.T) {
	tracked := trackedMarkdown(t)
	for i, doc := range docFiles {
		if slices.Contains(docFiles[:i], doc) {
			t.Errorf("%s is listed twice", doc)
		}
		if !slices.Contains(tracked, doc) {
			t.Errorf("%s is listed and not tracked", doc)
		}
		if len(extractGoFences(t, doc)) == 0 {
			t.Errorf("%s carries no Go fence, so the harness runs nothing in it", doc)
		}
	}
	for i, doc := range wholeProgramDocs {
		if slices.Contains(wholeProgramDocs[:i], doc) {
			t.Errorf("%s is listed twice as a whole-program document", doc)
		}
		if !slices.Contains(docFiles, doc) {
			t.Errorf("%s is a whole-program document the harness does not run", doc)
		}
	}
}

func TestEveryFenceOfAWholeProgramDocumentDeclaresPackageMain(t *testing.T) {
	for _, doc := range wholeProgramDocs {
		for _, f := range extractGoFences(t, doc) {
			if got := packageName(f.content); got != "main" {
				t.Errorf("%s opens with package %q, not main: a reader builds it as it stands", f.name(), got)
			}
		}
	}
}

func TestNoGoFenceHidesBehindASuffix(t *testing.T) {
	var hidden []string
	for _, doc := range trackedMarkdown(t) {
		data, err := os.ReadFile(filepath.Join(aletheia.RepoRoot(t), doc))
		if err != nil {
			t.Fatalf("read %s: %v", doc, err)
		}
		for i, line := range strings.Split(string(data), "\n") {
			if goFenceOpening(line) == hiddenGoFence {
				hidden = append(hidden, fmt.Sprintf("%s:%d", doc, i+1))
			}
		}
	}
	if len(hidden) > 0 {
		t.Errorf("Go fences the harness neither runs nor counts, a suffix on their info word: %v; "+
			"write go, or open a fence that cannot run with tildes", hidden)
	}
}

func TestAGoFenceIsReadByItsFirstInfoWord(t *testing.T) {
	for _, c := range []struct {
		line string
		want fenceOpening
	}{
		{"```go", runGoFence},
		{"   ```go", runGoFence},
		{"```go notest", runGoFence},
		{"```go\tx", runGoFence},
		{"```go,ignore", hiddenGoFence},
		{"```go{.x}", hiddenGoFence},
		{"```go:main.go", hiddenGoFence},
		{"  ```go``` / ```cpp``` block", notAGoFence},
		{"```go `x`", notAGoFence},
		{"```golang", notAGoFence},
		{"```go_x", notAGoFence},
		{"```gomod", notAGoFence},
		{"```", notAGoFence},
		{"```text", notAGoFence},
	} {
		if got := goFenceOpening(c.line); got != c.want {
			t.Errorf("goFenceOpening(%q) = %d, want %d", c.line, got, c.want)
		}
	}
}

// minFences is the floor under the number of Go fences across the listed
// files.
const minFences = 8

func TestEveryDocFileHasAtLeastOneGoFenceCollectively(t *testing.T) {
	total := 0
	for _, file := range docFiles {
		total += len(extractGoFences(t, file))
	}
	if total < minFences {
		t.Fatalf("expected at least %d Go fences across the listed files, saw %d", minFences, total)
	}
}

// textBlocks is every preformatted block of the library packages' comments
// that is no example, named by its file and first line: godoc gives a block no
// language, so each is listed here, and any other block is code, which an
// Example function holds so that go test runs it. A cgo preamble, the comment
// above import "C", is the C source cgo compiles, so it is not read.
var textBlocks = map[string]string{
	"go/aletheia/doc.go":           "rts.cores_mismatch              (FFIBackend, Warn)",
	"go/aletheia/json_response.go": "Header:  [nvals:u16][nerrs:u16][nabss:u16][reasonBytes:u32]  (10 bytes)",
}

func TestTheLibraryCommentsHoldNoCodeBlock(t *testing.T) {
	root := aletheia.RepoRoot(t)
	seen := map[string]bool{}
	var parser comment.Parser
	for _, dir := range []string{"go/aletheia", "go/excel"} {
		paths, err := filepath.Glob(filepath.Join(root, dir, "*.go"))
		if err != nil {
			t.Fatalf("glob %s: %v", dir, err)
		}
		for _, path := range paths {
			if strings.HasSuffix(path, "_test.go") {
				continue
			}
			file, err := goparser.ParseFile(token.NewFileSet(), path, nil, goparser.ParseComments)
			if err != nil {
				t.Fatalf("parse %s: %v", path, err)
			}
			rel, err := filepath.Rel(root, path)
			if err != nil {
				t.Fatalf("relative path of %s: %v", path, err)
			}
			rel = filepath.ToSlash(rel)
			preambles := cgoPreambles(file)
			for _, group := range file.Comments {
				if preambles[group] {
					continue
				}
				for _, block := range parser.Parse(group.Text()).Content {
					code, ok := block.(*comment.Code)
					if !ok {
						continue
					}
					first, _, _ := strings.Cut(code.Text, "\n")
					if textBlocks[rel] == first {
						seen[rel] = true
						continue
					}
					t.Errorf("%s: a comment holds a code block opening %q, which no test runs; "+
						"write it as an Example function", rel, first)
				}
			}
		}
	}
	for rel, first := range textBlocks {
		if !seen[rel] {
			t.Errorf("%s holds no text block opening %q", rel, first)
		}
	}
}

// cgoPreambles is every comment of a file that documents an import of "C".
func cgoPreambles(file *ast.File) map[*ast.CommentGroup]bool {
	preambles := map[*ast.CommentGroup]bool{}
	for _, decl := range file.Decls {
		gen, ok := decl.(*ast.GenDecl)
		if !ok || gen.Tok != token.IMPORT {
			continue
		}
		for _, spec := range gen.Specs {
			if imp, ok := spec.(*ast.ImportSpec); ok && imp.Path.Value == `"C"` {
				preambles[gen.Doc] = true
				preambles[imp.Doc] = true
			}
		}
	}
	return preambles
}
