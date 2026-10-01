// SPDX-FileCopyrightText: 2025 Nicolas Pelletier
// SPDX-License-Identifier: BSD-2-Clause

// The documents the doc-example harness runs, the extractor it reads their Go
// fences with, and the gates around them: a tracked document with a Go fence
// is listed and a listed one is tracked and carries one, the way the Python
// harness's list is held; no tracked document hides a Go fence from the
// extractor behind a suffixed info word; and the listed files keep a floor of
// fences. None of it needs the kernel, so it builds without cgo.

package aletheia_test

import (
	"bufio"
	"fmt"
	"os"
	"os/exec"
	"path/filepath"
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

// goFence is one Go fence of a listed file.
type goFence struct {
	file    string // path relative to the repository root
	line    int    // 1-based line number of the opening ```go
	content string // body between fences (no surrounding ``` lines)
}

func (f goFence) name() string {
	return fmt.Sprintf("%s:L%d", f.file, f.line)
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
		lineno     int
	)
	for scanner.Scan() {
		lineno++
		line := scanner.Text()
		if !inFence {
			if goFenceOpening(line) == runGoFence {
				inFence = true
				fenceStart = lineno
				fenceBody.Reset()
			}
			continue
		}
		if strings.TrimSpace(line) == "```" {
			fences = append(fences, goFence{
				file:    file,
				line:    fenceStart,
				content: fenceBody.String(),
			})
			inFence = false
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
