// SPDX-FileCopyrightText: 2025 Nicolas Pelletier
// SPDX-License-Identifier: BSD-2-Clause

// The documents the doc-example harness runs, the extractor it reads their Go
// fences with, and the two gates holding that list to the tree the way the
// Python harness's list is held: a tracked document with a Go fence is listed,
// and a listed one is tracked and carries one. None of it needs the kernel,
// so it builds without cgo.

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
)

// docFiles is every tracked Markdown file carrying a Go fence, less those
// unrunDocs names, relative to this directory.
var docFiles = []string{
	"../README.md",
	"../../docs/PITCH.md",
	"../../docs/architecture/CANCELLATION.md",
	"../../docs/reference/INTERFACES.md",
	"../../docs/reference/GO_API.md",
	"../../docs/development/DISTRIBUTION.md",
	"../../docs/guides/TUTORIAL.md",
}

// unrunDocs is every tracked document whose Go fences the harness does not
// run: the changelog's describe past releases.
var unrunDocs = []string{
	"../../CHANGELOG.md",
}

// goFence is one Go fence of a listed file.
type goFence struct {
	file    string // path relative to this directory
	line    int    // 1-based line number of the opening ```go
	content string // body between fences (no surrounding ``` lines)
}

func (f goFence) name() string {
	return fmt.Sprintf("%s:L%d", repoRelative(f.file), f.line)
}

// repoRelative turns a path relative to this directory into the
// repository-relative one git lists and subtests are named by.
func repoRelative(file string) string {
	return filepath.ToSlash(filepath.Join("go/aletheia", file))
}

// extractGoFences returns every Go fence of one file: an opening line whose
// info string is exactly go, closed by a line that is exactly the fence.
func extractGoFences(t *testing.T, file string) []goFence {
	t.Helper()
	data, err := os.ReadFile(file)
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
		trim := strings.TrimLeft(line, " \t")
		if !inFence {
			if strings.HasPrefix(trim, "```go") {
				rest := strings.TrimPrefix(trim, "```go")
				if rest == "" || rest[0] == ' ' || rest[0] == '\t' {
					inFence = true
					fenceStart = lineno
					fenceBody.Reset()
				}
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
	out, err := exec.Command("git", "-C", "../..", "ls-files", "-z", "--", "*.md", "*.mdx", "*.svx").Output()
	if err != nil {
		t.Fatalf("git ls-files: %v", err)
	}
	return strings.FieldsFunc(string(out), func(r rune) bool { return r == 0 })
}

func TestEveryTrackedGoFenceIsInAListedDocument(t *testing.T) {
	var known []string
	for _, file := range slices.Concat(docFiles, unrunDocs) {
		known = append(known, repoRelative(file))
	}
	var unlisted []string
	for _, doc := range trackedMarkdown(t) {
		if !slices.Contains(known, doc) && len(extractGoFences(t, filepath.Join("../..", doc))) > 0 {
			unlisted = append(unlisted, doc)
		}
	}
	if len(unlisted) > 0 {
		t.Errorf("Go fences the harness does not run: %v", unlisted)
	}
}

func TestEveryListedDocumentIsTrackedAndCarriesAGoFence(t *testing.T) {
	tracked := trackedMarkdown(t)
	for i, file := range docFiles {
		doc := repoRelative(file)
		if slices.Contains(docFiles[:i], file) {
			t.Errorf("%s is listed twice", doc)
		}
		if !slices.Contains(tracked, doc) {
			t.Errorf("%s is listed and not tracked", doc)
		}
		if len(extractGoFences(t, file)) == 0 {
			t.Errorf("%s carries no Go fence, so the harness runs nothing in it", doc)
		}
	}
}
