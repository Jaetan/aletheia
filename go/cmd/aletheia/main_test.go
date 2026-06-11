// SPDX-FileCopyrightText: 2025 Nicolas Pelletier
// SPDX-License-Identifier: BSD-2-Clause

package main

import (
	"os"
	"path/filepath"
	"testing"
)

// repoPath joins the test's package dir (go/cmd/aletheia) up to the repo root.
func repoPath(parts ...string) string {
	return filepath.Join(append([]string{"..", "..", ".."}, parts...)...)
}

// ensureLib points the CLI at the real libaletheia-ffi.so (via $ALETHEIA_LIB),
// skipping the test when the library has not been built — mirroring the
// binding's existing FFI tests, which exercise the real Agda core, never a stub.
func ensureLib(t *testing.T) {
	t.Helper()
	if os.Getenv("ALETHEIA_LIB") != "" {
		return
	}
	so := repoPath("build", "libaletheia-ffi.so")
	if _, err := os.Stat(so); err != nil {
		t.Skip("libaletheia-ffi.so not found — run 'cabal run shake -- build'")
	}
	t.Setenv("ALETHEIA_LIB", so)
}

// silenceStdout discards CLI stdout for the duration of a test so subcommand
// output does not clutter `go test -v`.
func silenceStdout(t *testing.T) {
	t.Helper()
	devnull, err := os.OpenFile(os.DevNull, os.O_WRONLY, 0)
	if err != nil {
		t.Fatalf("open %s: %v", os.DevNull, err)
	}
	old := os.Stdout
	os.Stdout = devnull
	t.Cleanup(func() {
		os.Stdout = old
		_ = devnull.Close()
	})
}

func TestCLISmoke(t *testing.T) {
	ensureLib(t)
	silenceStdout(t)
	dbc := repoPath("examples", "example.dbc")
	cases := [][]string{
		{"validate", "--dbc", dbc},
		{"validate", "--dbc", dbc, "--json"},
		{"signals", "--dbc", dbc},
		{"signals", "--dbc", dbc, "--json"},
		{"format-dbc", "--dbc", dbc},
		{"extract", "--dbc", dbc, "0x100", "102700000A000000"},
		{"extract", "--dbc", dbc, "0x100", "102700000A000000", "--json"}, // flag after positionals
		{"mux-query", "--dbc", repoPath("python", "tests", "fixtures", "dbc_corpus", "multiplexing.dbc"), "0x64"},
	}
	for _, args := range cases {
		if code := run(args); code != exitOK {
			t.Errorf("run(%v) = %d, want %d", args, code, exitOK)
		}
	}
}

func TestCLICheckDeferred(t *testing.T) {
	// `check` is intentionally absent (needs a verified CAN-log reader,
	// Phase 6 item) — it must report an error, not silently succeed.
	if code := run([]string{"check"}); code != exitError {
		t.Errorf("run([check]) = %d, want %d", code, exitError)
	}
}

func TestCLIUnknownCommand(t *testing.T) {
	if code := run([]string{"bogus"}); code != exitError {
		t.Errorf("run([bogus]) = %d, want %d", code, exitError)
	}
}

func TestReorderArgs(t *testing.T) {
	// Flags after positionals must be hoisted ahead of them; "--flag value"
	// pulls its value, bool flags do not.
	got := reorderArgs([]string{"0x100", "DATA", "--dbc", "f.dbc", "--json"},
		map[string]bool{"json": true})
	want := []string{"--dbc", "f.dbc", "--json", "0x100", "DATA"}
	if len(got) != len(want) {
		t.Fatalf("reorderArgs len = %d (%v), want %d (%v)", len(got), got, len(want), want)
	}
	for i := range want {
		if got[i] != want[i] {
			t.Errorf("reorderArgs[%d] = %q, want %q (full: %v)", i, got[i], want[i], got)
		}
	}
}
