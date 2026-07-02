// SPDX-FileCopyrightText: 2025 Nicolas Pelletier
// SPDX-License-Identifier: BSD-2-Clause

package main

import (
	"bytes"
	"io"
	"os"
	"path/filepath"
	"strings"
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

// captureStdout runs fn with os.Stdout redirected to a pipe and returns what it
// wrote, so a test can assert the CLI's text output (not just its exit code).
func captureStdout(t *testing.T, fn func()) string {
	t.Helper()
	r, w, err := os.Pipe()
	if err != nil {
		t.Fatalf("os.Pipe: %v", err)
	}
	old := os.Stdout
	os.Stdout = w
	defer func() { os.Stdout = old }() // restore even if fn panics

	// Drain the pipe in a goroutine so a large write can't fill the buffer and
	// deadlock before fn returns.
	done := make(chan string, 1)
	go func() {
		var buf bytes.Buffer
		_, _ = io.Copy(&buf, r)
		done <- buf.String()
	}()

	fn()
	_ = w.Close()
	return <-done
}

// TestCLISignalsRendersFactorExactly: a fine-resolution factor (1/8192 =
// 0.0001220703125) renders exactly via the kernel format_rational, never the
// lossy 6-significant-figure %g form ("0.00012207"). example.dbc has no such
// fine factor, so write a dedicated temp DBC.
func TestCLISignalsRendersFactorExactly(t *testing.T) {
	ensureLib(t)
	dir := t.TempDir()
	dbcPath := filepath.Join(dir, "fine.dbc")
	const dbc = "VERSION \"\"\n\nNS_ :\n\nBS_:\n\nBU_:\n\n" +
		"BO_ 1024 FineMsg: 8 ECU4\n" +
		" SG_ FineSignal : 0|16@1+ (0.0001220703125,0) [0|8] \"x\" Vector__XXX\n"
	if err := os.WriteFile(dbcPath, []byte(dbc), 0o600); err != nil {
		t.Fatalf("write dbc: %v", err)
	}
	out := captureStdout(t, func() {
		if code := run([]string{"signals", "--dbc", dbcPath}); code != exitOK {
			t.Fatalf("signals exit = %d, want %d", code, exitOK)
		}
	})
	if !strings.Contains(out, "x0.0001220703125") {
		t.Errorf("signals output missing the exact factor 0.0001220703125; got:\n%s", out)
	}
}

func TestCLISmoke(t *testing.T) {
	ensureLib(t)
	silenceStdout(t)
	dbc := repoPath("examples", "example.dbc")
	mux := repoPath("python", "tests", "fixtures", "dbc_corpus", "multiplexing.dbc")
	cases := [][]string{
		{"validate", "--dbc", dbc},
		{"validate", "--dbc", dbc, "--json"},
		{"signals", "--dbc", dbc},
		{"signals", "--dbc", dbc, "--json"},
		{"format-dbc", "--dbc", dbc},
		{"extract", "--dbc", dbc, "0x100", "102700000A000000"},
		{"extract", "--dbc", dbc, "0x100", "102700000A000000", "--json"}, // flag after positionals
		{"mux-query", "--dbc", mux, "0x64"},
		{"mux-query", "--dbc", mux, "0x64", "--mux", "Mode", "--value", "1"},
		{"mux-query", "--dbc", mux, "0x64", "--mux", "Mode", "--value", "1", "--json"},
	}
	for _, args := range cases {
		if code := run(args); code != exitOK {
			t.Errorf("run(%v) = %d, want %d", args, code, exitOK)
		}
	}
	// mux-query selector mismatch: --mux without --value must error (CoPilot PR #21).
	if code := run([]string{"mux-query", "--dbc", mux, "0x64", "--mux", "Mode"}); code != exitError {
		t.Errorf("mux-query --mux without --value = %d, want %d", code, exitError)
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
