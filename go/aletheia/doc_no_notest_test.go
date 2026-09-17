// SPDX-FileCopyrightText: 2025 Nicolas Pelletier
// SPDX-License-Identifier: BSD-2-Clause

// Two structural gates beside the doc-example harness: no listed file may
// hide a Go fence from it with a notest annotation (a fence that cannot run
// takes the text info string, as the Python rule has it), and the listed
// files together must keep carrying live Go examples, so a mass rename of
// info strings cannot silently empty the harness.

package aletheia_test

import (
	"bytes"
	"fmt"
	"os"
	"regexp"
	"testing"
)

// goNotestPattern is the notest annotation on a Go fence; the word boundary
// keeps a longer word containing "notest" from matching.
var goNotestPattern = regexp.MustCompile(`<!--\s*go\b[^>]*\bnotest\b[^>]*-->`)

func TestNoNotestGoFences(t *testing.T) {
	for _, file := range docFiles {
		t.Run(file, func(t *testing.T) {
			data, err := os.ReadFile(file)
			if err != nil {
				t.Fatalf("read %s: %v", file, err)
			}
			var offenders []string
			for _, m := range goNotestPattern.FindAllIndex(data, -1) {
				offenders = append(offenders, fmt.Sprintf("L%d", bytes.Count(data[:m[0]], []byte{'\n'})+1))
			}
			if len(offenders) > 0 {
				t.Errorf("%s has notest annotations at %v: switch the fence to the text info string, or drop the annotation and let it run", file, offenders)
			}
		})
	}
}

// minFences is the floor under the number of Go fences across the listed
// files; a single file may carry none.
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
