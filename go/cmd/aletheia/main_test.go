// SPDX-FileCopyrightText: 2025 Nicolas Pelletier
// SPDX-License-Identifier: BSD-2-Clause

package main

import (
	"bytes"
	"encoding/json"
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

// TestCLIValidateInvalidDBC: a DBC that parses syntactically but fails
// structural validation must render the numbered issue list (the same output
// as a has-errors ValidateDBC result) and exit 1 — not die with the bare
// message and exit 2. Derives the invalid DBC from the valid minimal.dbc
// fixture by duplicating a signal name in the text.
func TestCLIValidateInvalidDBC(t *testing.T) {
	ensureLib(t)
	src, err := os.ReadFile(repoPath("python", "tests", "fixtures", "dbc_corpus", "minimal.dbc"))
	if err != nil {
		t.Fatalf("read minimal.dbc fixture: %v", err)
	}
	broken := strings.Replace(string(src), "EngineTemp", "EngineSpeed", 1)
	if broken == string(src) {
		t.Fatal("fixture no longer contains EngineTemp; cannot derive duplicate-signal DBC")
	}
	dbcPath := filepath.Join(t.TempDir(), "broken.dbc")
	if err := os.WriteFile(dbcPath, []byte(broken), 0o600); err != nil {
		t.Fatalf("write dbc: %v", err)
	}

	t.Run("text lists issues and exits 1", func(t *testing.T) {
		out := captureStdout(t, func() {
			if code := run([]string{"validate", "--dbc", dbcPath}); code != exitViolations {
				t.Errorf("validate exit = %d, want %d", code, exitViolations)
			}
		})
		if !strings.Contains(out, "Validation FAILED") {
			t.Errorf("output missing the FAILED header; got:\n%s", out)
		}
		if !strings.Contains(out, "1. [ERROR] duplicate_signal_name") {
			t.Errorf("output missing the numbered duplicate_signal_name issue; got:\n%s", out)
		}
	})

	t.Run("json emits the has_errors fail shape", func(t *testing.T) {
		var code int
		out := captureStdout(t, func() {
			code = run([]string{"validate", "--dbc", dbcPath, "--json"})
		})
		// The exit code reflects the validation outcome in both output
		// modes: --json on a has_errors result exits 1 like text mode.
		if code != exitViolations {
			t.Errorf("validate --json exit = %d, want %d", code, exitViolations)
		}
		var payload struct {
			Status    string           `json:"status"`
			HasErrors bool             `json:"has_errors"`
			Total     int              `json:"total_issues"`
			Issues    []map[string]any `json:"issues"`
		}
		if err := json.Unmarshal([]byte(out), &payload); err != nil {
			t.Fatalf("output is not valid JSON: %v\n%s", err, out)
		}
		if payload.Status != "fail" || !payload.HasErrors {
			t.Errorf("status/has_errors = %q/%v, want fail/true", payload.Status, payload.HasErrors)
		}
		if payload.Total != len(payload.Issues) || len(payload.Issues) == 0 {
			t.Fatalf("total_issues = %d with %d issues, want a consistent non-empty list",
				payload.Total, len(payload.Issues))
		}
		found := false
		for _, issue := range payload.Issues {
			if issue["code"] == "duplicate_signal_name" {
				found = true
			}
		}
		if !found {
			t.Errorf("issues missing duplicate_signal_name; got %v", payload.Issues)
		}
	})

	t.Run("unparseable dbc still dies with exit 2", func(t *testing.T) {
		garbagePath := filepath.Join(t.TempDir(), "garbage.dbc")
		if err := os.WriteFile(garbagePath, []byte("this is not a dbc\n"), 0o600); err != nil {
			t.Fatalf("write dbc: %v", err)
		}
		if code := run([]string{"validate", "--dbc", garbagePath}); code != exitError {
			t.Errorf("validate on unparseable dbc = %d, want %d", code, exitError)
		}
	})

	t.Run("other subcommands still die with exit 2", func(t *testing.T) {
		silenceStdout(t)
		if code := run([]string{"signals", "--dbc", dbcPath}); code != exitError {
			t.Errorf("signals on invalid dbc = %d, want %d", code, exitError)
		}
	})
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
