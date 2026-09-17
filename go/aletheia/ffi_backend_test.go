//go:build cgo && linux

// SPDX-FileCopyrightText: 2025 Nicolas Pelletier
// SPDX-License-Identifier: BSD-2-Clause

package aletheia_test

import (
	"bytes"
	"context"
	"errors"
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

// ---------------------------------------------------------------------------
// NewFFIBackendFromEnv — ALETHEIA_LIB resolution (env-symmetry with Python/Rust)
// ---------------------------------------------------------------------------
// The empty-check branch is exercised WITHOUT a real .so so it stays covered by
// mutation testing: unset yields a Validation error and a set-but-missing path
// yields an FFI (dlopen) error, and the two distinct Kinds are what kill a
// dropped or inverted empty-check. Only the happy path below needs the .so.

func TestNewFFIBackendFromEnv_UnsetIsValidationError(t *testing.T) {
	t.Setenv("ALETHEIA_LIB", "") // force empty; t.Setenv restores afterward
	_, err := aletheia.NewFFIBackendFromEnv()
	if err == nil {
		t.Fatal("expected an error when ALETHEIA_LIB is unset, got nil")
	}
	var e *aletheia.Error
	if !errors.As(err, &e) {
		t.Fatalf("expected *aletheia.Error, got %T: %v", err, err)
	}
	if e.Kind != aletheia.ErrValidation {
		t.Errorf("Kind = %v, want ErrValidation (unset is a usage error, not an FFI failure)", e.Kind)
	}
}

func TestNewFFIBackendFromEnv_MissingPathIsFFIError(t *testing.T) {
	t.Setenv("ALETHEIA_LIB", "/nonexistent/libaletheia-ffi.so")
	_, err := aletheia.NewFFIBackendFromEnv()
	if err == nil {
		t.Fatal("expected a dlopen error for a nonexistent ALETHEIA_LIB path, got nil")
	}
	var e *aletheia.Error
	if !errors.As(err, &e) {
		t.Fatalf("expected *aletheia.Error, got %T: %v", err, err)
	}
	if e.Kind != aletheia.ErrFFI {
		t.Errorf("Kind = %v, want ErrFFI (a set-but-missing path must reach dlopen, not the unset guard)", e.Kind)
	}
}

func TestNewFFIBackendFromEnv_LoadsRealLibrary(t *testing.T) {
	lib := findFFILib()
	if lib == "" {
		t.Skip("libaletheia-ffi.so not found — run 'cabal run shake -- build' first")
	}
	t.Setenv("ALETHEIA_LIB", lib)
	b, err := aletheia.NewFFIBackendFromEnv()
	if err != nil {
		t.Fatalf("NewFFIBackendFromEnv with a real ALETHEIA_LIB: %v", err)
	}
	if b == nil {
		t.Fatal("expected a non-nil backend")
	}
}

// ffiEndpointDBC is the one-message fixture the endpoint tests below build
// frames against: one unsigned little-endian signal, sixteen bits wide, a
// quarter per count.
const ffiEndpointDBC = "VERSION \"\"\n\nNS_ :\n\nBS_:\n\nBU_: ECU\n\n" +
	"BO_ 256 Msg: 8 ECU\n SG_ Sig : 0|16@1+ (0.25,0) [0|8000] \"u\" ECU\n\n"

// ffiEndpointClient boots a client on the real library with that DBC loaded,
// and the message identifier and length to address it with.
func ffiEndpointClient(t *testing.T) (*aletheia.Client, aletheia.CANID, aletheia.DLC) {
	t.Helper()
	lib := findFFILib()
	if lib == "" {
		t.Skip("libaletheia-ffi.so not found; run 'cabal run shake -- build' first")
	}
	backend, err := aletheia.NewFFIBackend(lib)
	if err != nil {
		t.Fatalf("NewFFIBackend: %v", err)
	}
	client, err := aletheia.NewClient(backend)
	if err != nil {
		t.Fatalf("NewClient: %v", err)
	}
	t.Cleanup(func() {
		if err := client.Close(); err != nil {
			t.Errorf("Close: %v", err)
		}
	})
	if _, err := client.ParseDBCText(context.Background(), ffiEndpointDBC); err != nil {
		t.Fatalf("ParseDBCText: %v", err)
	}
	id, err := aletheia.NewStandardID(256)
	if err != nil {
		t.Fatalf("NewStandardID: %v", err)
	}
	dlc, err := aletheia.NewDLC(8)
	if err != nil {
		t.Fatalf("NewDLC: %v", err)
	}
	return client, id, dlc
}

// FormatDBCBinary answers the DBC the session holds, through the real library.
func TestFFIBackend_FormatDBCBinaryReturnsTheLoadedDBC(t *testing.T) {
	client, _, _ := ffiEndpointClient(t)
	dbc, err := client.FormatDBC(context.Background())
	if err != nil {
		t.Fatalf("FormatDBC: %v", err)
	}
	if len(dbc.Messages) != 1 {
		t.Fatalf("messages = %d, want 1", len(dbc.Messages))
	}
	if dbc.Messages[0].Name != "Msg" {
		t.Errorf("message name = %q, want \"Msg\"", dbc.Messages[0].Name)
	}
	if len(dbc.Messages[0].Signals) != 1 || dbc.Messages[0].Signals[0].Name != "Sig" {
		t.Errorf("signals = %+v, want the one signal Sig", dbc.Messages[0].Signals)
	}
}

// BuildFrameBin and UpdateFrameBin place the signal at the bits the DBC gives
// it, through the real library. A quarter per count puts the physical 100 at
// the raw 400, little-endian at bit zero.
func TestFFIBackend_BuildAndUpdateFrameBinPlaceTheSignal(t *testing.T) {
	client, id, dlc := ffiEndpointClient(t)
	ctx := context.Background()
	built, err := client.BuildFrame(ctx, id, dlc, []aletheia.SignalValue{
		{Name: "Sig", Value: aletheia.Rational{Numerator: 100, Denominator: 1}},
	})
	if err != nil {
		t.Fatalf("BuildFrame: %v", err)
	}
	if want := []byte{0x90, 0x01, 0, 0, 0, 0, 0, 0}; !bytes.Equal(built, want) {
		t.Errorf("built payload = % x, want % x", built, want)
	}
	updated, err := client.UpdateFrame(ctx, id, dlc, built, []aletheia.SignalValue{
		{Name: "Sig", Value: aletheia.Rational{Numerator: 4, Denominator: 1}},
	})
	if err != nil {
		t.Fatalf("UpdateFrame: %v", err)
	}
	if want := []byte{0x10, 0x00, 0, 0, 0, 0, 0, 0}; !bytes.Equal(updated, want) {
		t.Errorf("updated payload = % x, want % x", updated, want)
	}
}

// SendErrorBinary and SendRemoteBinary carry their events into a real stream,
// which ends without a warning about either.
func TestFFIBackend_SendErrorAndSendRemoteBinaryStream(t *testing.T) {
	client, id, _ := ffiEndpointClient(t)
	ctx := context.Background()
	if err := client.StartStream(ctx); err != nil {
		t.Fatalf("StartStream: %v", err)
	}
	if err := client.SendError(ctx, aletheia.Timestamp{Microseconds: 1000}); err != nil {
		t.Fatalf("SendError: %v", err)
	}
	if err := client.SendRemote(ctx, aletheia.Timestamp{Microseconds: 2000}, id); err != nil {
		t.Fatalf("SendRemote: %v", err)
	}
	result, err := client.EndStream(ctx)
	if err != nil {
		t.Fatalf("EndStream: %v", err)
	}
	if len(result.Warnings) != 0 {
		t.Errorf("warnings = %+v, want none", result.Warnings)
	}
}

// A timestamp before the epoch is refused at the boundary, without reaching
// the library, by both event endpoints.
func TestFFIBackend_NegativeTimestampIsRefused(t *testing.T) {
	lib := findFFILib()
	if lib == "" {
		t.Skip("libaletheia-ffi.so not found; run 'cabal run shake -- build' first")
	}
	backend, err := aletheia.NewFFIBackend(lib)
	if err != nil {
		t.Fatalf("NewFFIBackend: %v", err)
	}
	state, err := backend.Init()
	if err != nil {
		t.Fatalf("Init: %v", err)
	}
	defer backend.Close(state)
	past := aletheia.Timestamp{Microseconds: -1}
	id, err := aletheia.NewStandardID(256)
	if err != nil {
		t.Fatalf("NewStandardID: %v", err)
	}
	if _, err := backend.SendErrorBinary(state, past); err == nil {
		t.Error("SendErrorBinary took a negative timestamp")
	}
	if _, err := backend.SendRemoteBinary(state, past, id); err == nil {
		t.Error("SendRemoteBinary took a negative timestamp")
	}
}

// StablePtrCount counts the sessions the process holds: one more while a
// session is open, and back where it started once it is closed.
func TestFFIBackend_StablePtrCountTracksOpenSessions(t *testing.T) {
	lib := findFFILib()
	if lib == "" {
		t.Skip("libaletheia-ffi.so not found; run 'cabal run shake -- build' first")
	}
	backend, err := aletheia.NewFFIBackend(lib)
	if err != nil {
		t.Fatalf("NewFFIBackend: %v", err)
	}
	before := aletheia.StablePtrCount()
	state, err := backend.Init()
	if err != nil {
		t.Fatalf("Init: %v", err)
	}
	if open := aletheia.StablePtrCount(); open != before+1 {
		t.Errorf("count with one session open = %d, want %d", open, before+1)
	}
	backend.Close(state)
	if after := aletheia.StablePtrCount(); after != before {
		t.Errorf("count after closing = %d, want %d", after, before)
	}
}

// A value the signal cannot hold is refused by the kernel, and both binary
// frame endpoints carry the message it minted rather than a status number.
func TestFFIBackend_BinaryFrameRefusalCarriesTheKernelMessage(t *testing.T) {
	client, id, dlc := ffiEndpointClient(t)
	ctx := context.Background()
	tooLarge := []aletheia.SignalValue{
		{Name: "Sig", Value: aletheia.Rational{Numerator: 100000, Denominator: 1}},
	}
	for name, call := range map[string]func() (aletheia.FramePayload, error){
		"BuildFrame": func() (aletheia.FramePayload, error) { return client.BuildFrame(ctx, id, dlc, tooLarge) },
		"UpdateFrame": func() (aletheia.FramePayload, error) {
			return client.UpdateFrame(ctx, id, dlc, make(aletheia.FramePayload, 8), tooLarge)
		},
	} {
		t.Run(name, func(t *testing.T) {
			payload, err := call()
			if err == nil {
				t.Fatalf("a value outside the signal range built % x instead of failing", payload)
			}
			var e *aletheia.Error
			if !errors.As(err, &e) {
				t.Fatalf("error is %T, want *aletheia.Error", err)
			}
			if e.Kind != aletheia.ErrProtocol {
				t.Errorf("Kind = %v, want ErrProtocol", e.Kind)
			}
			if !strings.Contains(err.Error(), "signal 'Sig'") {
				t.Errorf("error %q does not name the signal the kernel refused", err)
			}
			if payload != nil {
				t.Errorf("payload = % x, want none on a refusal", payload)
			}
		})
	}
}
