//go:build cgo && linux

// SPDX-License-Identifier: BSD-2-Clause

// B.3.j — DBC text parser cross-binding parity gate (Go side).
//
// Scope. This is a binding-layer integration test on a finite fixture corpus.
// It does NOT extend, replace, or stand in for the universal Agda roundtrip
// theorem proven in B.3.d (∀ d → WellFormedDBC d → parseText (formatText d) ≡
// inj₂ d, in Aletheia/DBC/TextParser/Properties/Substrate/Unsafe.agda). Parser
// correctness is established by that proof, universally over the DBC domain.
// What this test validates instead is that the Go binding's wire-to-native
// conversion (Agda JSON → DbcDefinition) preserves the wire bytes faithfully.
// A failure here means the Go binding lost or mangled fields on parse, not
// that the Agda parser is wrong.
//
// The committed parity snapshots in
// python/tests/fixtures/dbc_corpus/parity_snapshots/ are the cross-binding
// oracle — the Python (test_dbc_corpus_parity.py) and C++
// (dbc_corpus_parity_tests.cpp) tests assert byte equality against the same
// files. When all three match, the bindings have observed identical
// DbcDefinition structure for every fixture.
//
// Canonical form: sorted JSON keys + 2-space indent + trailing newline + the
// "emit int when denominator=1" rule (already shared by the binding's
// internal serializer). Go produces this naturally via json.MarshalIndent on
// a map[string]any (which sorts keys), with one post-processing step to drop
// "extended": false from message envelopes (Agda's wire format omits
// "extended" for standard CAN frames; see attachCanID for the same convention
// on comment/attribute targets).

package aletheia

import (
	"bytes"
	"encoding/json"
	"os"
	"path/filepath"
	"sort"
	"testing"
)

// findFFILibForParityTest locates libaletheia-ffi.so. Returns "" if missing,
// triggering t.Skip — same pattern as TestFFIBackend_RTSCoresMismatchWarns.
func findFFILibForParityTest() string {
	if env := os.Getenv("ALETHEIA_LIB"); env != "" {
		if _, err := os.Stat(env); err == nil {
			return env
		}
	}
	candidates := []string{
		"../../build/libaletheia-ffi.so",
		"../build/libaletheia-ffi.so",
		"build/libaletheia-ffi.so",
	}
	for _, c := range candidates {
		abs, err := filepath.Abs(c)
		if err != nil {
			continue
		}
		if _, err := os.Stat(abs); err == nil {
			return abs
		}
	}
	return ""
}

// canonicalDBCJSON canonical-encodes a DbcDefinition for the parity test. The
// shape mirrors the Python FractionJSONEncoder + sort_keys=True + indent=2
// output. json.MarshalIndent on map[string]any sorts keys alphabetically by
// design (Go 1.12+); serializeDBC already mirrors the Agda wire form for
// "extended" (omitted on standard frames) and "presence" (explicit
// "always"), so no post-processing is needed.
func canonicalDBCJSON(dbc DbcDefinition) ([]byte, error) {
	m, err := serializeDBC(dbc)
	if err != nil {
		return nil, err
	}
	out, err := json.MarshalIndent(m, "", "  ")
	if err != nil {
		return nil, err
	}
	out = append(out, '\n')
	return out, nil
}

// TestDBCCorpusParity exercises every corpus DBC through the Go binding's
// real-FFI ParseDBCText and asserts byte-identical canonical output against
// the cross-binding parity snapshot. The corpus + snapshots live under the
// Python tree (python/tests/fixtures/dbc_corpus/) because Python authored
// them; Go simply consumes the same files.
func TestDBCCorpusParity(t *testing.T) {
	lib := findFFILibForParityTest()
	if lib == "" {
		t.Skip("libaletheia-ffi.so not found — run 'cabal run shake -- build' first")
	}

	backend, err := NewFFIBackend(lib)
	if err != nil {
		t.Fatalf("NewFFIBackend: %v", err)
	}

	client, err := NewClient(backend)
	if err != nil {
		t.Fatalf("NewClient: %v", err)
	}
	defer func() {
		if err := client.Close(); err != nil {
			t.Errorf("Close: %v", err)
		}
	}()

	corpusDir, err := filepath.Abs("../../python/tests/fixtures/dbc_corpus")
	if err != nil {
		t.Fatalf("resolve corpus dir: %v", err)
	}
	paritySnapshotDir := filepath.Join(corpusDir, "parity_snapshots")

	dbcFiles, err := filepath.Glob(filepath.Join(corpusDir, "*.dbc"))
	if err != nil {
		t.Fatalf("glob corpus: %v", err)
	}
	if len(dbcFiles) == 0 {
		t.Fatalf("no .dbc files under %s — corpus moved?", corpusDir)
	}
	sort.Strings(dbcFiles)

	for _, dbcPath := range dbcFiles {
		dbcPath := dbcPath // capture for subtest closure
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

			snapshotPath := filepath.Join(
				paritySnapshotDir, name[:len(name)-len(".dbc")]+".json",
			)
			expected, err := os.ReadFile(snapshotPath)
			if err != nil {
				t.Fatalf("read parity snapshot %s: %v", snapshotPath, err)
			}

			if !bytes.Equal(actual, expected) {
				// Write actual to a tmp path to make local debugging easy.
				tmp := filepath.Join(t.TempDir(), name+".actual.json")
				if writeErr := os.WriteFile(tmp, actual, 0o600); writeErr == nil {
					t.Errorf(
						"parity drift for %s — Go canonical output diverges from %s. "+
							"Wrote actual to %s for diff.",
						name, snapshotPath, tmp,
					)
				} else {
					t.Errorf(
						"parity drift for %s — Go canonical output diverges from %s.",
						name, snapshotPath,
					)
				}
			}
		})
	}
}
