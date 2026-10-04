//go:build cgo && linux

// SPDX-FileCopyrightText: 2025 Nicolas Pelletier
// SPDX-License-Identifier: BSD-2-Clause

package aletheia_test

import (
	"bytes"
	"context"
	"errors"
	"log/slog"
	"slices"
	"strings"
	"testing"
	"unsafe"

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

// ffiClient boots a client on the real library, holding no DBC, closed when
// the test ends.
func ffiClient(t *testing.T) *aletheia.Client {
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
		if err := client.Close(); err != nil {
			t.Errorf("Close: %v", err)
		}
	})
	return client
}

// ffiEndpointClient boots a client on the real library with that DBC loaded,
// and the message identifier and length to address it with.
func ffiEndpointClient(t *testing.T) (*aletheia.Client, aletheia.CANID, aletheia.DLC) {
	t.Helper()
	client := ffiClient(t)
	if _, err := client.ParseDBCText(t.Context(), ffiEndpointDBC); err != nil {
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
	dbc, err := client.FormatDBC(t.Context())
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
	ctx := t.Context()
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
	ctx := t.Context()
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

// ffiSession opens a session on the real library holding no DBC, closed when
// the test ends, for the tests that call the backend without a client.
func ffiSession(t *testing.T) (*aletheia.FFIBackend, unsafe.Pointer) {
	t.Helper()
	backend, err := aletheia.NewFFIBackend(requireFFILib(t))
	if err != nil {
		t.Fatalf("NewFFIBackend: %v", err)
	}
	state, err := backend.Init()
	if err != nil {
		t.Fatalf("Init: %v", err)
	}
	t.Cleanup(func() { backend.Close(state) })
	return backend, state
}

// A timestamp before the epoch is refused at the boundary, without reaching
// the library, by both event endpoints.
func TestFFIBackend_NegativeTimestampIsRefused(t *testing.T) {
	backend, state := ffiSession(t)
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
// frame endpoints carry the code and the message it minted rather than a
// status number: a value outside the declared [0, 8000], and one lying
// between two raw values at a quarter per count, which is refused rather
// than rounded to either.
func TestFFIBackend_BinaryFrameRefusalCarriesTheKernelMessage(t *testing.T) {
	client, id, dlc := ffiEndpointClient(t)
	ctx := t.Context()
	refusals := map[string]struct {
		value   aletheia.Rational
		code    string
		message string
	}{
		"above the declared maximum": {
			value:   aletheia.Rational{Numerator: 100000, Denominator: 1},
			code:    aletheia.CodeFrameValueOutOfRange,
			message: "value 100000 for signal 'Sig' is outside [0, 8000]",
		},
		"below the declared minimum": {
			value:   aletheia.Rational{Numerator: -1, Denominator: 1},
			code:    aletheia.CodeFrameValueOutOfRange,
			message: "value -1 for signal 'Sig' is outside [0, 8000]",
		},
		"between two raw values": {
			value:   aletheia.Rational{Numerator: 1, Denominator: 10},
			code:    aletheia.CodeFrameValueNotRepresentable,
			message: "no integer raw value scales to value 0.1 for signal 'Sig' (factor 0.25, offset 0)",
		},
	}
	for refusal, tc := range refusals {
		signals := []aletheia.SignalValue{{Name: "Sig", Value: tc.value}}
		for name, call := range map[string]func() (aletheia.FramePayload, error){
			"BuildFrame": func() (aletheia.FramePayload, error) { return client.BuildFrame(ctx, id, dlc, signals) },
			"UpdateFrame": func() (aletheia.FramePayload, error) {
				return client.UpdateFrame(ctx, id, dlc, make(aletheia.FramePayload, 8), signals)
			},
		} {
			t.Run(refusal+"/"+name, func(t *testing.T) {
				payload, err := call()
				if err == nil {
					t.Fatalf("the value built % x instead of failing", payload)
				}
				var e *aletheia.Error
				if !errors.As(err, &e) {
					t.Fatalf("error is %T, want *aletheia.Error", err)
				}
				if e.Kind != aletheia.ErrProtocol {
					t.Errorf("Kind = %v, want ErrProtocol", e.Kind)
				}
				if e.Code != tc.code {
					t.Errorf("Code = %q, want %q", e.Code, tc.code)
				}
				if e.Message != tc.message {
					t.Errorf("Message = %q, want %q", e.Message, tc.message)
				}
				if payload != nil {
					t.Errorf("payload = % x, want none on a refusal", payload)
				}
			})
		}
	}
}

// The declared bounds are inside the range a frame accepts, and a value on a
// raw step is placed exactly, by a build and by an update: the maximum writes
// raw 32000 and a quarter writes raw 1, both little-endian.
func TestFFIBackend_BinaryFrameBuildsTheBoundsAndTheSteps(t *testing.T) {
	client, id, dlc := ffiEndpointClient(t)
	cases := map[string]struct {
		value aletheia.Rational
		want  aletheia.FramePayload
	}{
		"the declared minimum": {aletheia.IntRational(0), aletheia.FramePayload{0, 0, 0, 0, 0, 0, 0, 0}},
		"the declared maximum": {aletheia.IntRational(8000), aletheia.FramePayload{0x00, 0x7D, 0, 0, 0, 0, 0, 0}},
		"one raw step":         {aletheia.Rational{Numerator: 1, Denominator: 4}, aletheia.FramePayload{0x01, 0, 0, 0, 0, 0, 0, 0}},
	}
	for name, tc := range cases {
		signals := []aletheia.SignalValue{{Name: "Sig", Value: tc.value}}
		for entry, call := range map[string]func(ctx context.Context) (aletheia.FramePayload, error){
			"BuildFrame": func(ctx context.Context) (aletheia.FramePayload, error) {
				return client.BuildFrame(ctx, id, dlc, signals)
			},
			"UpdateFrame": func(ctx context.Context) (aletheia.FramePayload, error) {
				return client.UpdateFrame(ctx, id, dlc, make(aletheia.FramePayload, 8), signals)
			},
		} {
			t.Run(name+"/"+entry, func(t *testing.T) {
				payload, err := call(t.Context())
				if err != nil {
					t.Fatalf("%s: %v", entry, err)
				}
				if !bytes.Equal(payload, tc.want) {
					t.Errorf("payload = % x, want % x", payload, tc.want)
				}
			})
		}
	}
}

// Two multiplexed signals over the same bits, requested together, are refused
// by a build and by an update alike: of two writes to one bit only the later
// would remain.
func TestFFIBackend_BinaryFrameRefusesTwoSignalsSharingABit(t *testing.T) {
	const mux = "VERSION \"\"\n\nNS_ :\n\nBS_:\n\nBU_: ECU\n\nBO_ 100 BasicMux: 8 ECU\n" +
		" SG_ Mode M : 0|4@1+ (1,0) [0|15] \"\" ECU\n" +
		" SG_ PayloadA m0 : 8|16@1+ (1,0) [0|65535] \"\" ECU\n" +
		" SG_ PayloadB m1 : 8|16@1+ (1,0) [0|65535] \"\" ECU\n\n"
	client := ffiClient(t)
	if _, err := client.ParseDBCText(t.Context(), mux); err != nil {
		t.Fatalf("ParseDBCText: %v", err)
	}
	id, err := aletheia.NewStandardID(100)
	if err != nil {
		t.Fatalf("NewStandardID: %v", err)
	}
	dlc, err := aletheia.NewDLC(8)
	if err != nil {
		t.Fatalf("NewDLC: %v", err)
	}
	signals := []aletheia.SignalValue{
		{Name: "PayloadA", Value: aletheia.IntRational(1)},
		{Name: "PayloadB", Value: aletheia.IntRational(1)},
	}
	for entry, call := range map[string]func(ctx context.Context) (aletheia.FramePayload, error){
		"BuildFrame": func(ctx context.Context) (aletheia.FramePayload, error) {
			return client.BuildFrame(ctx, id, dlc, signals)
		},
		"UpdateFrame": func(ctx context.Context) (aletheia.FramePayload, error) {
			return client.UpdateFrame(ctx, id, dlc, make(aletheia.FramePayload, 8), signals)
		},
	} {
		t.Run(entry, func(t *testing.T) {
			payload, err := call(t.Context())
			var e *aletheia.Error
			if !errors.As(err, &e) {
				t.Fatalf("error is %T (%v), want *aletheia.Error", err, err)
			}
			if e.Code != aletheia.CodeFrameSignalsOverlap || e.Message != "signals overlap" {
				t.Errorf("refusal = %q %q, want %q %q", e.Code, e.Message, aletheia.CodeFrameSignalsOverlap, "signals overlap")
			}
			if payload != nil {
				t.Errorf("payload = % x, want none on a refusal", payload)
			}
		})
	}
}

// A DBC whose declared range reaches past the values its signal's bits carry
// after scaling is refused at load, with one error naming range_exceeds_bits
// and the bound at fault: eight unsigned bits carry 0 to 255, eight signed
// bits -128 to 127.
func TestFFIBackend_DeclaredRangePastTheBitsIsRefused(t *testing.T) {
	const head = "VERSION \"\"\n\nNS_ :\n\nBS_:\n\nBU_: ECU\n\nBO_ 256 M: 8 ECU\n"
	const above = "Message 'M', signal 'S': declared maximum lies above the values its bits carry"
	const below = "Message 'M', signal 'S': declared minimum lies below the values its bits carry"
	cases := map[string]struct {
		signal string
		detail string
	}{
		"an unsigned maximum of 1000": {` SG_ S : 0|8@1+ (1,0) [0|1000] "" ECU`, above},
		"a signed maximum of 255":     {` SG_ S : 0|8@1- (1,0) [-128|255] "" ECU`, above},
		"an unsigned minimum of -10":  {` SG_ S : 0|8@1+ (1,0) [-10|255] "" ECU`, below},
	}
	for name, tc := range cases {
		t.Run(name, func(t *testing.T) {
			_, err := ffiClient(t).ParseDBCText(t.Context(), head+tc.signal+"\n\n")
			var vfe *aletheia.ValidationFailedError
			if !errors.As(err, &vfe) {
				t.Fatalf("error is %T (%v), want *aletheia.ValidationFailedError", err, err)
			}
			if vfe.Code != aletheia.CodeHandlerValidationFailed {
				t.Errorf("Code = %q, want %q", vfe.Code, aletheia.CodeHandlerValidationFailed)
			}
			if !vfe.HasErrors {
				t.Error("HasErrors = false, want true")
			}
			want := []aletheia.ValidationIssue{{
				Severity: aletheia.SeverityError, Code: aletheia.IssueRangeExceedsBits, Detail: tc.detail,
			}}
			if !slices.Equal(vfe.Issues, want) {
				t.Errorf("Issues = %+v, want %+v", vfe.Issues, want)
			}
		})
	}
}

// A binary entry's refusal carries the kernel's code, read from the error
// envelope the entry sets, beside the message the envelope holds rather than
// the envelope's text: a session holding no DBC is refused by each of the
// three with handler_no_dbc.
func TestFFIBackend_BinaryRefusalCarriesTheKernelCode(t *testing.T) {
	backend, state := ffiSession(t)
	id := standardID(t, 256)
	calls := map[string]func() ([]byte, error){
		"BuildFrameBin": func() ([]byte, error) { return backend.BuildFrameBin(state, id, dlc8(), nil) },
		"UpdateFrameBin": func() ([]byte, error) {
			return backend.UpdateFrameBin(state, id, dlc8(), make([]byte, 8), nil)
		},
		"ExtractSignalsBin": func() ([]byte, error) { return backend.ExtractSignalsBin(state, id, dlc8(), make([]byte, 8)) },
	}
	for name, call := range calls {
		t.Run(name, func(t *testing.T) {
			out, err := call()
			var e *aletheia.Error
			if !errors.As(err, &e) {
				t.Fatalf("error is %T (%v), want *aletheia.Error", err, err)
			}
			if e.Code != aletheia.CodeHandlerNoDBC {
				t.Errorf("Code = %q, want %q", e.Code, aletheia.CodeHandlerNoDBC)
			}
			if e.Kind != aletheia.ErrProtocol {
				t.Errorf("Kind = %v, want ErrProtocol", e.Kind)
			}
			if e.Message == "" || strings.HasPrefix(e.Message, "{") {
				t.Errorf("Message = %q, want the envelope's message", e.Message)
			}
			if out != nil {
				t.Errorf("output = % x, want none on a refusal", out)
			}
		})
	}
}

// ffiEdgeDBC carries the two lengths at the ends of what a frame can be: a
// CAN-FD message of sixty-four bytes whose one signal is the last byte, and a
// message of no bytes and no signal.
const ffiEdgeDBC = "VERSION \"\"\n\nNS_ :\n\nBS_:\n\nBU_: ECU\n\n" +
	"BO_ 512 Fd: 64 ECU\n SG_ Last : 504|8@1+ (1,0) [0|255] \"\" ECU\n\n" +
	"BO_ 768 Empty: 0 ECU\n\n"

// ffiEdgeClient boots a client on the real library with ffiEdgeDBC loaded.
func ffiEdgeClient(t *testing.T) *aletheia.Client {
	t.Helper()
	client := ffiClient(t)
	if _, err := client.ParseDBCText(t.Context(), ffiEdgeDBC); err != nil {
		t.Fatalf("ParseDBCText: %v", err)
	}
	return client
}

// A payload of the CAN-FD maximum crosses the boundary whole, through the
// real library, and its last byte is read back.
func TestFFIBackend_ASixtyFourBytePayloadCrosses(t *testing.T) {
	client := ffiEdgeClient(t)
	dlc, err := aletheia.BytesToDLC(64)
	if err != nil {
		t.Fatalf("BytesToDLC: %v", err)
	}
	payload := make(aletheia.FramePayload, 64)
	payload[63] = 7
	result, err := client.ExtractSignals(t.Context(), standardID(t, 512), dlc, payload)
	if err != nil {
		t.Fatalf("ExtractSignals: %v", err)
	}
	if len(result.Values) != 1 || result.Values[0].Name != "Last" || result.Values[0].Value != aletheia.IntRational(7) {
		t.Errorf("Values = %+v, want Last = 7", result.Values)
	}
}

// Each backend entry that carries a payload holds it to the byte count its DLC
// names, before anything is copied across the boundary: twenty bytes under a
// DLC of eight are refused though a CAN-FD frame holds them, and so are
// sixty-five under the code for sixty-four. The exact count crosses, and what
// answers it is the kernel: a response from the two entries answering JSON,
// and from the two answering bytes the kernel's coded refusal of a session
// holding no DBC, where the guard's refusal carries no code.
func TestFFIBackend_APayloadNotItsDLCByteCountIsRefused(t *testing.T) {
	backend, state := ffiSession(t)
	id := standardID(t, 256)
	entries := map[string]func(dlc aletheia.DLC, data []byte) error{
		"SendFrameBinary": func(dlc aletheia.DLC, data []byte) error {
			_, err := backend.SendFrameBinary(state, aletheia.Timestamp{}, id, dlc, data, nil, nil)
			return err
		},
		"ExtractSignalsBinary": func(dlc aletheia.DLC, data []byte) error {
			_, err := backend.ExtractSignalsBinary(state, id, dlc, data)
			return err
		},
		"UpdateFrameBin": func(dlc aletheia.DLC, data []byte) error {
			_, err := backend.UpdateFrameBin(state, id, dlc, data, nil)
			return err
		},
		"ExtractSignalsBin": func(dlc aletheia.DLC, data []byte) error {
			_, err := backend.ExtractSignalsBin(state, id, dlc, data)
			return err
		},
	}
	refused := map[string]struct {
		code   uint8
		length int
	}{
		"twenty bytes under DLC 8":      {8, 20},
		"sixty-five bytes under DLC 15": {15, 65},
	}
	for name, call := range entries {
		t.Run(name, func(t *testing.T) {
			for what, tc := range refused {
				dlc, err := aletheia.NewDLC(tc.code)
				if err != nil {
					t.Fatalf("NewDLC(%d): %v", tc.code, err)
				}
				err = call(dlc, make([]byte, tc.length))
				requireKind(t, err, aletheia.ErrValidation)
				if !strings.Contains(err.Error(), "does not match DLC") {
					t.Errorf("%s: error %q does not name the DLC it failed", what, err)
				}
			}
			err := call(dlc8(), make([]byte, 8))
			var e *aletheia.Error
			if err != nil && (!errors.As(err, &e) || e.Code == "") {
				t.Errorf("the exact byte count did not reach the kernel: %v", err)
			}
		})
	}
}

// A message of no bytes builds to an empty payload through the real library:
// the backend hands the kernel no buffer to write rather than the address of
// an element an empty slice does not have.
func TestFFIBackend_BuildsAFrameOfNoBytes(t *testing.T) {
	client := ffiEdgeClient(t)
	dlc, err := aletheia.NewDLC(0)
	if err != nil {
		t.Fatalf("NewDLC: %v", err)
	}
	built, err := client.BuildFrame(t.Context(), standardID(t, 768), dlc, nil)
	if err != nil {
		t.Fatalf("BuildFrame: %v", err)
	}
	if len(built) != 0 {
		t.Errorf("built % x, want no bytes", built)
	}
}

// The trace's first instant, timestamp zero, is taken by each of the three
// event entries through the real library.
func TestFFIBackend_TimestampZeroIsTaken(t *testing.T) {
	client, id, dlc := ffiEndpointClient(t)
	ctx := t.Context()
	if err := client.StartStream(ctx); err != nil {
		t.Fatalf("StartStream: %v", err)
	}
	zero := aletheia.Timestamp{}
	if _, err := client.SendFrame(ctx, zero, id, dlc, make(aletheia.FramePayload, 8), nil, nil); err != nil {
		t.Fatalf("SendFrame: %v", err)
	}
	if err := client.SendError(ctx, zero); err != nil {
		t.Fatalf("SendError: %v", err)
	}
	if err := client.SendRemote(ctx, zero, id); err != nil {
		t.Fatalf("SendRemote: %v", err)
	}
	if _, err := client.EndStream(ctx); err != nil {
		t.Fatalf("EndStream: %v", err)
	}
}
