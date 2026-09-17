//go:build cgo && linux

// SPDX-FileCopyrightText: 2025 Nicolas Pelletier
// SPDX-License-Identifier: BSD-2-Clause

// The Go side of the DBC text parser parity gate over the fixture corpus.
//
// Parser correctness is the universal Agda theorem (for every well-formed d,
// parseText (formatText d) is d, in
// Aletheia/DBC/TextParser/Properties/Substrate/Unsafe.agda), which this test
// neither extends nor replaces. What it checks is that the Go binding's
// conversion of the kernel's JSON into a DBCDefinition loses nothing: a
// failure means the binding dropped or mangled a field, not that the parser
// is wrong.
//
// The committed snapshots under python/tests/fixtures/dbc_corpus/
// parity_snapshots/ are the cross-binding oracle; the Python
// (test_dbc_corpus_parity.py) and C++ (dbc_corpus_parity_tests.cpp) tests
// compare against the same files, so when all three pass the bindings have
// seen the same structure for every fixture. The canonical form is sorted
// keys, two-space indent, a trailing newline, and an integer where the
// denominator is 1, which the binding's own serializer already writes.

package aletheia

import (
	"bytes"
	"encoding/json"
	"os"
	"path/filepath"
	"slices"
	"strings"
	"testing"
)

// canonicalDBCJSON encodes a DBCDefinition in the snapshots' form: serializeDBC
// marshals a map, so its keys are sorted, and MarshalIndent re-indents the
// returned RawMessage without reordering.
func canonicalDBCJSON(dbc DBCDefinition) ([]byte, error) {
	m, err := serializeDBC(dbc)
	if err != nil {
		return nil, err
	}
	out, err := json.MarshalIndent(m, "", "  ")
	if err != nil {
		return nil, err
	}
	return append(out, '\n'), nil
}

// Every corpus DBC parsed through the real library canonicalises to its
// snapshot byte for byte, and every snapshot has its fixture.
func TestDBCCorpusParity(t *testing.T) {
	lib := findFFILibrary()
	if lib == "" {
		t.Skip("libaletheia-ffi.so not found; run 'cabal run shake -- build' first")
	}
	backend, err := NewFFIBackend(lib)
	if err != nil {
		t.Fatalf("NewFFIBackend: %v", err)
	}
	client, err := NewClient(backend)
	if err != nil {
		t.Fatalf("NewClient: %v", err)
	}
	t.Cleanup(func() {
		if err := client.Close(); err != nil {
			t.Errorf("Close: %v", err)
		}
	})

	corpusDir, err := filepath.Abs("../../python/tests/fixtures/dbc_corpus")
	if err != nil {
		t.Fatalf("resolve corpus dir: %v", err)
	}
	snapshotDir := filepath.Join(corpusDir, "parity_snapshots")
	dbcFiles, err := filepath.Glob(filepath.Join(corpusDir, "*.dbc"))
	if err != nil {
		t.Fatalf("glob corpus: %v", err)
	}
	if len(dbcFiles) == 0 {
		t.Fatalf("no .dbc files under %s", corpusDir)
	}
	slices.Sort(dbcFiles)

	snapshots, err := filepath.Glob(filepath.Join(snapshotDir, "*.json"))
	if err != nil {
		t.Fatalf("glob snapshots: %v", err)
	}
	for _, snap := range snapshots {
		fixture := filepath.Join(corpusDir, strings.TrimSuffix(filepath.Base(snap), ".json")+".dbc")
		if _, err := os.Stat(fixture); err != nil {
			t.Errorf("snapshot %s has no fixture %s", filepath.Base(snap), filepath.Base(fixture))
		}
	}

	for _, dbcPath := range dbcFiles {
		name := filepath.Base(dbcPath)
		t.Run(name, func(t *testing.T) {
			text, err := os.ReadFile(dbcPath)
			if err != nil {
				t.Fatalf("read %s: %v", name, err)
			}
			parsed, err := client.ParseDBCText(ctx, string(text))
			if err != nil {
				t.Fatalf("ParseDBCText(%s): %v", name, err)
			}
			actual, err := canonicalDBCJSON(parsed.DBC)
			if err != nil {
				t.Fatalf("canonicalDBCJSON(%s): %v", name, err)
			}
			snapshotPath := filepath.Join(snapshotDir, strings.TrimSuffix(name, ".dbc")+".json")
			expected, err := os.ReadFile(snapshotPath)
			if err != nil {
				t.Fatalf("read parity snapshot %s: %v", snapshotPath, err)
			}
			if !bytes.Equal(actual, expected) {
				tmp := filepath.Join(t.TempDir(), name+".actual.json")
				where := ""
				if os.WriteFile(tmp, actual, 0o600) == nil {
					where = " Wrote the Go output to " + tmp + " for a diff."
				}
				t.Errorf("parity drift for %s: the Go canonical output diverges from %s.%s", name, snapshotPath, where)
			}
		})
	}
}
