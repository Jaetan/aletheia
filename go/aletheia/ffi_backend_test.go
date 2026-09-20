//go:build cgo && linux

// SPDX-FileCopyrightText: 2025 Nicolas Pelletier
// SPDX-License-Identifier: BSD-2-Clause

package aletheia_test

import (
	"bytes"
	"context"
	"errors"
	"log/slog"
	"strings"
	"testing"

	"github.com/Jaetan/aletheia/go/v5/aletheia"
)

// requireFFILib is that path, or the reason to skip: a test that reaches the
// kernel cannot run without the library.
func requireFFILib(t *testing.T) string {
	t.Helper()
	lib := aletheia.FindFFILibrary()
	if lib == "" {
		t.Skip("libaletheia-ffi.so not found; run 'cabal run shake -- build' first")
	}
	return lib
}

// ffiBackendLog opens a backend with the options and answers what it logged.
// The capture is the backend's own logger, the one WithFFILogger sets: the
// runtime warning does not go to the client's logger, so a test watching that
// one would pass whatever the backend did.
func ffiBackendLog(t *testing.T, lib string, opts ...aletheia.FFIBackendOption) string {
	t.Helper()
	var buf bytes.Buffer
	logger := slog.New(slog.NewJSONHandler(&buf, &slog.HandlerOptions{Level: slog.LevelDebug}))
	if _, err := aletheia.NewFFIBackend(lib, append(opts, aletheia.WithFFILogger(logger))...); err != nil {
		t.Fatalf("NewFFIBackend: %v", err)
	}
	return buf.String()
}

// startRuntime opens a backend with no options, which starts the GHC runtime
// on one core if this is the first of the process and finds it started
// otherwise, so the tests below know which count is active.
func startRuntime(t *testing.T, lib string) {
	t.Helper()
	if _, err := aletheia.NewFFIBackend(lib); err != nil {
		t.Fatalf("NewFFIBackend: %v", err)
	}
}

// The GHC runtime starts once per process, so a later backend asking for
// another core count is told which count is running. The record carries both
// numbers, since the point is to show the caller what it got.
func TestFFIBackend_RTSCoresMismatchWarns(t *testing.T) {
	lib := requireFFILib(t)
	startRuntime(t, lib)
	output := ffiBackendLog(t, lib, aletheia.WithRTSCores(8))
	for _, want := range []string{"rts.cores_mismatch", `"level":"WARN"`, `"requested_cores":8`, `"active_cores":1`} {
		if !strings.Contains(output, want) {
			t.Errorf("the log does not carry %s: %s", want, output)
		}
	}
}

// Asking for the count already running says nothing.
func TestFFIBackend_RTSCoresMatchingSilent(t *testing.T) {
	lib := requireFFILib(t)
	startRuntime(t, lib)
	output := ffiBackendLog(t, lib, aletheia.WithRTSCores(1))
	for _, unwanted := range []string{"rts.cores_mismatch", `"level":"WARN"`} {
		if strings.Contains(output, unwanted) {
			t.Errorf("the log carries %s though the counts match: %s", unwanted, output)
		}
	}
}

// An unset ALETHEIA_LIB is the caller's mistake, not a loader failure, and the
// two tests below tell the kinds apart so that dropping or inverting the empty
// check fails. Neither needs the library, which is what keeps the check under
// the mutation lane on a machine that has not built it.
func TestNewFFIBackendFromEnv_UnsetIsValidationError(t *testing.T) {
	t.Setenv("ALETHEIA_LIB", "")
	_, err := aletheia.NewFFIBackendFromEnv()
	if err == nil {
		t.Fatal("expected an error when ALETHEIA_LIB is unset, got nil")
	}
	var e *aletheia.Error
	if !errors.As(err, &e) {
		t.Fatalf("expected *aletheia.Error, got %T: %v", err, err)
	}
	if e.Kind != aletheia.ErrValidation {
		t.Errorf("Kind = %v, want ErrValidation: unset is a usage error, not a loader failure", e.Kind)
	}
}

// A path that is set but names nothing reaches the loader, which is the other
// side of the same check.
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
		t.Errorf("Kind = %v, want ErrFFI: a set path must reach the loader, not the unset guard", e.Kind)
	}
}

// A path that names the library opens it.
func TestNewFFIBackendFromEnv_LoadsRealLibrary(t *testing.T) {
	lib := requireFFILib(t)
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
	backend, err := aletheia.NewFFIBackend(requireFFILib(t))
	if err != nil {
		t.Fatalf("NewFFIBackend: %v", err)
	}
	client, err := aletheia.NewClient(backend)
	if err != nil {
		t.Fatalf("NewClient: %v", err)
	}
	t.Cleanup(func() {
		if err := closeWithin(t, client); err != nil {
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
	backend, err := aletheia.NewFFIBackend(requireFFILib(t))
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
	backend, err := aletheia.NewFFIBackend(requireFFILib(t))
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
