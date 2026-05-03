// Cat 32 structural gate: every ```go fence in the published docs must run.
//
// Mirror of python/tests/test_doc_examples_harness.py. The execution invariant
// — that every runnable ```go fence actually compiles and runs end-to-end — is
// enforced by TestDocExamples. THIS test enforces the *escape-hatch* invariant:
// no `<!-- go notest -->` annotation may appear in the tracked doc surface.
//
// Pseudocode and design-sketch fences (function signatures, partial method
// definitions, interface shapes) must use the `text` info string so they are
// invisible to the harness. The Python rule is identical: `python notest` is
// banned; non-runnable fences flip to `text`.
package aletheia_test

import (
	"bytes"
	"fmt"
	"os"
	"regexp"
	"testing"
)

// goNotestPattern matches `<!-- go notest -->` HTML-comment annotations,
// the only mechanism that could hide a Go fence from TestDocExamples.
// `\bnotest\b` ensures we don't false-positive on substrings.
var goNotestPattern = regexp.MustCompile(`<!--\s*go\b[^>]*\bnotest\b[^>]*-->`)

// TestNoNotestGoFences rejects `<!-- go notest -->` annotations across every
// tracked doc file. A genuinely non-runnable fence must change its info
// string from `go` to `text`, mirroring the Python rule.
func TestNoNotestGoFences(t *testing.T) {
	for _, file := range docFiles {
		file := file
		t.Run(file, func(t *testing.T) {
			data, err := os.ReadFile(file)
			if err != nil {
				t.Fatalf("read %s: %v", file, err)
			}
			matches := goNotestPattern.FindAllIndex(data, -1)
			if len(matches) == 0 {
				return
			}
			var offenders []string
			for _, m := range matches {
				line := bytes.Count(data[:m[0]], []byte{'\n'}) + 1
				offenders = append(offenders, fmt.Sprintf("L%d", line))
			}
			t.Errorf("%s has `<!-- go notest -->` annotations at %v — switch the "+
				"fence info string from `go` to `text` (or drop the annotation so "+
				"the harness runs the block).", file, offenders)
		})
	}
}

// TestEveryDocFileHasAtLeastOneGoFenceCollectively guards against a mass
// rename (e.g. someone converting every `go` info string to `text` during
// a refactor) that would silently remove the doc-example surface. We don't
// require every individual file to carry a fence — some are prose-heavy —
// but the collective set must have live examples.
func TestEveryDocFileHasAtLeastOneGoFenceCollectively(t *testing.T) {
	total := 0
	for _, file := range docFiles {
		fences := extractGoFences(t, file)
		total += len(fences)
	}
	const minFences = 8
	if total < minFences {
		t.Fatalf("expected the doc-example harness to cover ≥%d ```go fences "+
			"across the tracked docs, saw %d", minFences, total)
	}
}
