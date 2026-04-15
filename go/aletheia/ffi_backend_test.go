//go:build cgo && linux

package aletheia_test

import (
	"bytes"
	"log/slog"
	"os"
	"path/filepath"
	"strings"
	"testing"

	"github.com/aletheia-automotive/aletheia-go/aletheia"
)

// ---------------------------------------------------------------------------
// WithRTSCores mismatch warning (2026-04-09)
// ---------------------------------------------------------------------------
// NewFFIBackend initializes the GHC RTS exactly once per process. Subsequent
// calls with a WithRTSCores value that differs from the active cores count
// must emit a slog.Warn record with active_cores and requested_cores fields.
// These tests use a captured slog handler to verify the warning semantics
// without relying on the default stderr handler.

// findFFILib locates libaletheia-ffi.so relative to the go package,
// mirroring the search strategy in go/benchmarks/main.go. Returns the
// empty string if the library cannot be found.
func findFFILib() string {
	// Environment override (CI / custom builds).
	if env := os.Getenv("ALETHEIA_LIB"); env != "" {
		if _, err := os.Stat(env); err == nil {
			return env
		}
	}
	// Project build directory, relative to go/aletheia.
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

func TestFFIBackend_RTSCoresMismatchWarns(t *testing.T) {
	lib := findFFILib()
	if lib == "" {
		t.Skip("libaletheia-ffi.so not found — run 'cabal run shake -- build' first")
	}

	// Establish deterministic RTS state: first call initializes to 1 if the
	// RTS has not yet been touched this process, else a no-op.
	b1, err := aletheia.NewFFIBackend(lib)
	if err != nil {
		t.Fatalf("first NewFFIBackend: %v", err)
	}
	_ = b1

	// Second call with different rts_cores must log a warning via WithFFILogger.
	var buf bytes.Buffer
	logger := slog.New(slog.NewJSONHandler(&buf, &slog.HandlerOptions{Level: slog.LevelDebug}))
	b2, err := aletheia.NewFFIBackend(lib, aletheia.WithRTSCores(8), aletheia.WithFFILogger(logger))
	if err != nil {
		t.Fatalf("second NewFFIBackend: %v", err)
	}
	_ = b2
	output := buf.String()

	if !strings.Contains(output, "rts.cores_mismatch") {
		t.Errorf("expected 'rts.cores_mismatch' in slog output, got: %s", output)
	}
	if !strings.Contains(output, `"level":"WARN"`) {
		t.Errorf("expected WARN level in slog output, got: %s", output)
	}
	if !strings.Contains(output, `"requested_cores":8`) {
		t.Errorf("expected requested_cores=8 in slog output, got: %s", output)
	}
	if !strings.Contains(output, `"active_cores":1`) {
		t.Errorf("expected active_cores=1 in slog output, got: %s", output)
	}
}

func TestFFIBackend_RTSCoresMatchingSilent(t *testing.T) {
	lib := findFFILib()
	if lib == "" {
		t.Skip("libaletheia-ffi.so not found — run 'cabal run shake -- build' first")
	}

	// Ensure the RTS is initialized (to 1 cores) from this or a prior test.
	b1, err := aletheia.NewFFIBackend(lib)
	if err != nil {
		t.Fatalf("first NewFFIBackend: %v", err)
	}
	_ = b1

	// Matching rts_cores=1 must not emit a warning via WithFFILogger.
	// Note: the mismatch warning is emitted to the FFIBackend's logger
	// (set by WithFFILogger), not the Client logger (WithLogger); capturing
	// the wrong logger in this test historically made it vacuously pass.
	var buf bytes.Buffer
	logger := slog.New(slog.NewJSONHandler(&buf, &slog.HandlerOptions{Level: slog.LevelDebug}))
	b2, err := aletheia.NewFFIBackend(lib, aletheia.WithRTSCores(1), aletheia.WithFFILogger(logger))
	if err != nil {
		t.Fatalf("second NewFFIBackend: %v", err)
	}
	_ = b2
	output := buf.String()

	if strings.Contains(output, "rts.cores_mismatch") {
		t.Errorf("expected no rts.cores_mismatch record, got: %s", output)
	}
	if strings.Contains(output, `"level":"WARN"`) {
		t.Errorf("expected no WARN-level record, got: %s", output)
	}
}
