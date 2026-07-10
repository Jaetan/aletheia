// SPDX-FileCopyrightText: 2025 Nicolas Pelletier
// SPDX-License-Identifier: BSD-2-Clause

package aletheia_test

import (
	"errors"
	"slices"
	"testing"

	"github.com/aletheia-automotive/aletheia-go/aletheia"
)

func TestErrorResponse(t *testing.T) {
	mock := aletheia.NewMockBackend(
		aletheia.Respond(`{"status":"error","code":"handler_no_dbc","message":"no DBC loaded"}`),
	)
	c, err := aletheia.NewClient(mock)
	if err != nil {
		t.Fatal(err)
	}
	defer c.Close()

	_, err = c.FormatDBC(ctx)
	if err == nil {
		t.Fatal("expected error")
	}
	var aErr *aletheia.Error
	if !errors.As(err, &aErr) {
		t.Fatalf("expected *aletheia.Error, got %T", err)
	}
	if aErr.Kind != aletheia.ErrProtocol {
		t.Errorf("expected ErrProtocol, got %s", aErr.Kind)
	}
}

func TestBackendError(t *testing.T) {
	mock := aletheia.NewMockBackend(
		aletheia.RespondErr(aletheia.NewMockError("connection lost")),
	)
	c, err := aletheia.NewClient(mock)
	if err != nil {
		t.Fatal(err)
	}
	defer c.Close()

	_, err = c.ParseDBC(ctx, testDBC())
	if err == nil {
		t.Fatal("expected error from backend")
	}
}

func TestMockBackendExhaustion(t *testing.T) {
	mock := aletheia.NewMockBackend() // no responses
	c, err := aletheia.NewClient(mock)
	if err != nil {
		t.Fatal(err)
	}
	defer c.Close()

	_, err = c.ParseDBC(ctx, testDBC())
	if err == nil {
		t.Fatal("expected error when mock exhausted")
	}
}

func TestUseAfterClose(t *testing.T) {
	mock := aletheia.NewMockBackend(
		aletheia.Respond(`{"status":"success"}`),
	)
	c, err := aletheia.NewClient(mock)
	if err != nil {
		t.Fatal(err)
	}
	c.Close()

	// Calling after Close should return a state error, not crash.
	_, err = c.ParseDBC(ctx, testDBC())
	if err == nil {
		t.Fatal("expected error after Close")
	}
	var aErr *aletheia.Error
	if !errors.As(err, &aErr) {
		t.Fatalf("expected *aletheia.Error, got %T", err)
	}
	if aErr.Kind != aletheia.ErrState {
		t.Errorf("expected ErrState, got %s", aErr.Kind)
	}

	// Double-close should be safe.
	c.Close()
}

func TestErrorKindString(t *testing.T) {
	tests := []struct {
		kind aletheia.ErrorKind
		want string
	}{
		{aletheia.ErrProtocol, "protocol"},
		{aletheia.ErrValidation, "validation"},
		{aletheia.ErrState, "state"},
		{aletheia.ErrFFI, "ffi"},
		{aletheia.ErrorKind(99), "ErrorKind(99)"},
	}
	for _, tt := range tests {
		if got := tt.kind.String(); got != tt.want {
			t.Errorf("ErrorKind(%d).String() = %q, want %q", tt.kind, got, tt.want)
		}
	}
}

func TestDoubleClose(t *testing.T) {
	mock := aletheia.NewMockBackend()
	c, err := aletheia.NewClient(mock)
	if err != nil {
		t.Fatal(err)
	}
	if err := c.Close(); err != nil {
		t.Errorf("first close: %v", err)
	}
	if err := c.Close(); err != nil {
		t.Errorf("second close: %v", err)
	}
}

// ---------------------------------------------------------------------------
// Parse error codes from the PhysicallyValid gate (2026-04-08, 2026-05-15)
// ---------------------------------------------------------------------------
// DBC/JSONParser.agda's physicalGate enforces parse-time constraints. Both
// byte orders require bitLength ≥ 1 (LE was previously permissive on
// bl=0, deferring to the validator's BitLengthZero warning — now
// uniformly rejected at the parse boundary, completing BE-LE parity).
// BigEndian additionally enforces two
// roundtrip-shape constraints:
//
//   • bitLength ≥ 1                     → SignalBitLengthZero (BE + LE)
//   • csb + bl − 1 < frameBytes * 8      → SignalOverflowsFrame (BE only)
//   • bl − 1 ≤ csb                      → SignalMSBBelowBitLength (BE only)
//
// Go's surface for this layer is JSON error-code parsing — the actual
// physicalGate logic lives in Agda and is verified by the real-FFI
// C++/Python tests (both byte orders covered after the 2026-05-15 LE
// parity completion). These tests exercise the Go binding's JSON
// error-code extraction via MockBackend, ensuring the codes round-trip
// through parseErrorResponse into aErr.Code with the expected
// ErrProtocol kind.

func TestParseError_SignalBitLengthZero(t *testing.T) {
	mock := aletheia.NewMockBackend(
		aletheia.Respond(`{
			"status": "error",
			"code": "parse_signal_bit_length_zero",
			"message": "signal bit length must be at least 1"
		}`),
	)
	c, err := aletheia.NewClient(mock)
	if err != nil {
		t.Fatal(err)
	}
	defer c.Close()

	_, err = c.ParseDBC(ctx, testDBC())
	if err == nil {
		t.Fatal("expected parse error")
	}
	var aErr *aletheia.Error
	if !errors.As(err, &aErr) {
		t.Fatalf("expected *aletheia.Error, got %T", err)
	}
	if aErr.Code != aletheia.CodeParseSignalBitLengthZero {
		t.Errorf("expected code %q, got %q", aletheia.CodeParseSignalBitLengthZero, aErr.Code)
	}
	if aErr.Kind != aletheia.ErrProtocol {
		t.Errorf("expected ErrProtocol, got %s", aErr.Kind)
	}
}

func TestParseError_SignalOverflowsFrame(t *testing.T) {
	mock := aletheia.NewMockBackend(
		aletheia.Respond(`{
			"status": "error",
			"code": "parse_signal_overflows_frame",
			"message": "signal overflows frame: startBit=0 bitLength=33 frameBytes=4"
		}`),
	)
	c, err := aletheia.NewClient(mock)
	if err != nil {
		t.Fatal(err)
	}
	defer c.Close()

	_, err = c.ParseDBC(ctx, testDBC())
	if err == nil {
		t.Fatal("expected parse error")
	}
	var aErr *aletheia.Error
	if !errors.As(err, &aErr) {
		t.Fatalf("expected *aletheia.Error, got %T", err)
	}
	if aErr.Code != aletheia.CodeParseSignalOverflowsFrame {
		t.Errorf("expected code %q, got %q", aletheia.CodeParseSignalOverflowsFrame, aErr.Code)
	}
	if aErr.Kind != aletheia.ErrProtocol {
		t.Errorf("expected ErrProtocol, got %s", aErr.Kind)
	}
}

func TestParseError_SignalMSBBelowBitLength(t *testing.T) {
	mock := aletheia.NewMockBackend(
		aletheia.Respond(`{
			"status": "error",
			"code": "parse_signal_msb_below_bit_length",
			"message": "signal MSB below bitLength: csb=0 bl=2"
		}`),
	)
	c, err := aletheia.NewClient(mock)
	if err != nil {
		t.Fatal(err)
	}
	defer c.Close()

	_, err = c.ParseDBC(ctx, testDBC())
	if err == nil {
		t.Fatal("expected parse error")
	}
	var aErr *aletheia.Error
	if !errors.As(err, &aErr) {
		t.Fatalf("expected *aletheia.Error, got %T", err)
	}
	if aErr.Code != aletheia.CodeParseSignalMSBBelowBitLength {
		t.Errorf("expected code %q, got %q", aletheia.CodeParseSignalMSBBelowBitLength, aErr.Code)
	}
	if aErr.Kind != aletheia.ErrProtocol {
		t.Errorf("expected ErrProtocol, got %s", aErr.Kind)
	}
}

func TestParseError_CodeConstantsExported(t *testing.T) {
	// Regression guard: the three parse error codes added in 2026-04-08 must
	// remain exported as public constants with the exact string values that
	// Agda emits. These are matched directly by application code that wants
	// to react to specific parse errors (e.g. "signal bit length zero" →
	// "try re-exporting with a wider bit length"), so a typo would silently
	// break error-recovery logic in downstream tools.
	tests := []struct {
		name string
		got  string
		want string
	}{
		{"SignalBitLengthZero", aletheia.CodeParseSignalBitLengthZero, "parse_signal_bit_length_zero"},
		{"SignalOverflowsFrame", aletheia.CodeParseSignalOverflowsFrame, "parse_signal_overflows_frame"},
		{"SignalMSBBelowBitLength", aletheia.CodeParseSignalMSBBelowBitLength, "parse_signal_msb_below_bit_length"},
		{"NonTerminatingRational", aletheia.CodeParseNonTerminatingRational, "parse_non_terminating_rational"},
		{"NonIntegerMultiplexValue", aletheia.CodeParseNonIntegerMultiplexValue, "parse_non_integer_multiplex_value"},
	}
	for _, tt := range tests {
		if tt.got != tt.want {
			t.Errorf("%s = %q, want %q", tt.name, tt.got, tt.want)
		}
	}
}

func TestParseError_NonTerminatingRational(t *testing.T) {
	// Commit 3/6 (EV_ ℚ→DecRat migration) introduces this failure mode:
	// a Rational with a denominator that isn't 2^a·5^b has no terminating
	// decimal expansion, so fromℚ? returns nothing and the parser emits
	// parse_non_terminating_rational.  Mock exercises the Go binding's
	// decode path for the new code; Python/C++ integration tests cover
	// the actual FFI → Agda round-trip.
	mock := aletheia.NewMockBackend(
		aletheia.Respond(`{
			"status": "error",
			"code": "parse_non_terminating_rational",
			"message": "rational field 'initial' has no terminating decimal expansion"
		}`),
	)
	c, err := aletheia.NewClient(mock)
	if err != nil {
		t.Fatal(err)
	}
	defer c.Close()

	_, err = c.ParseDBC(ctx, testDBC())
	if err == nil {
		t.Fatal("expected parse error")
	}
	var aErr *aletheia.Error
	if !errors.As(err, &aErr) {
		t.Fatalf("expected *aletheia.Error, got %T", err)
	}
	if aErr.Code != aletheia.CodeParseNonTerminatingRational {
		t.Errorf("expected code %q, got %q", aletheia.CodeParseNonTerminatingRational, aErr.Code)
	}
	if aErr.Kind != aletheia.ErrProtocol {
		t.Errorf("expected ErrProtocol, got %s", aErr.Kind)
	}
}

// TestMockBackend_ErrorsOnQueueExhaustion pins the queue-exhaustion contract
// (#108 cross-binding unification): an empty MockBackend queue is a harness
// misconfiguration, so Process returns a typed ErrState error rather than
// fabricating a default response.  Mirrors the C++ sibling "MockBackend throws
// on queue exhaustion" (cpp/tests/unit_tests_client.cpp) and the Python/Rust
// siblings.  The starved request is recorded BEFORE the error, so Inputs()
// stays populated on the erroring call.
func TestMockBackend_ErrorsOnQueueExhaustion(t *testing.T) {
	// wantStateError asserts err is a non-nil *aletheia.Error of kind ErrState
	// whose Message is exactly wantMsg.  The exported Message field carries the
	// bare diagnostic; (*Error).Error() prefixes "aletheia state error: ", so
	// pinning Message directly is the tightest available assertion.
	wantStateError := func(t *testing.T, err error, wantMsg string) {
		t.Helper()
		if err == nil {
			t.Fatal("expected error on exhausted queue, got nil")
		}
		var aErr *aletheia.Error
		if !errors.As(err, &aErr) {
			t.Fatalf("expected *aletheia.Error, got %T", err)
		}
		if aErr.Kind != aletheia.ErrState {
			t.Errorf("expected ErrState, got %s", aErr.Kind)
		}
		if aErr.Message != wantMsg {
			t.Errorf("Message = %q, want %q", aErr.Message, wantMsg)
		}
	}

	// --- Empty queue: both the JSON control-plane and the binary shim starve. ---
	empty := aletheia.NewMockBackend() // no responses
	state, err := empty.Init()
	if err != nil {
		t.Fatal(err)
	}

	// (1) JSON path → op token "process".
	jsonCmd := `{"command":"setProperties","formulas":[]}`
	_, err = empty.Process(state, jsonCmd)
	wantStateError(t, err, "mock backend: no queued response for process")

	// (2) Binary path → op token "<binary:sendFrame>".  Args are zero-ish but
	// validly constructed; SendFrameBinary ignores them beyond recording the
	// sentinel input.
	id, err := aletheia.NewStandardID(0)
	if err != nil {
		t.Fatal(err)
	}
	dlc, err := aletheia.NewDLC(0)
	if err != nil {
		t.Fatal(err)
	}
	_, err = empty.SendFrameBinary(state, aletheia.Timestamp{}, id, dlc, nil, nil, nil)
	wantStateError(t, err, "mock backend: no queued response for <binary:sendFrame>")

	// (3) Record-before-error: the starved calls are still recorded, so Inputs()
	// stays populated even though both Process calls returned an error.
	inputs := empty.Inputs()
	if !slices.Contains(inputs, jsonCmd) {
		t.Errorf("Inputs() = %q, want it to contain the starved JSON input %q", inputs, jsonCmd)
	}
	if !slices.Contains(inputs, "<binary:sendFrame>") {
		t.Errorf("Inputs() = %q, want it to contain the starved binary sentinel", inputs)
	}

	// (4) A queued response takes priority over the error path; once drained,
	// the next call re-drains and errors again (the error path is re-entrant,
	// not one-shot).
	primed := aletheia.NewMockBackend(aletheia.Respond(`{"custom":true}`))
	pState, err := primed.Init()
	if err != nil {
		t.Fatal(err)
	}
	got, err := primed.Process(pState, jsonCmd)
	if err != nil {
		t.Fatalf("queued response should not error: %v", err)
	}
	if got != `{"custom":true}` {
		t.Errorf("Process = %q, want the queued response %q", got, `{"custom":true}`)
	}
	_, err = primed.Process(pState, jsonCmd)
	wantStateError(t, err, "mock backend: no queued response for process")
}

func TestParseError_NonIntegerMultiplexValue(t *testing.T) {
	// Non-integer in `multiplex_values` JSON array.
	// Previously, the Agda parser emitted `parse_invalid_presence` with
	// the literal `"non-integer in multiplex_values"`, conflating two
	// failure modes on a single wire code.  This regression guard
	// asserts the typed `parse_non_integer_multiplex_value` code reaches
	// the Go decode path intact.
	mock := aletheia.NewMockBackend(
		aletheia.Respond(`{
			"status": "error",
			"code": "parse_non_integer_multiplex_value",
			"message": "non-integer value in 'multiplex_values' array (every element must be a JSON natural number)"
		}`),
	)
	c, err := aletheia.NewClient(mock)
	if err != nil {
		t.Fatal(err)
	}
	defer c.Close()

	_, err = c.ParseDBC(ctx, testDBC())
	if err == nil {
		t.Fatal("expected parse error")
	}
	var aErr *aletheia.Error
	if !errors.As(err, &aErr) {
		t.Fatalf("expected *aletheia.Error, got %T", err)
	}
	if aErr.Code != aletheia.CodeParseNonIntegerMultiplexValue {
		t.Errorf("expected code %q, got %q", aletheia.CodeParseNonIntegerMultiplexValue, aErr.Code)
	}
	if aErr.Kind != aletheia.ErrProtocol {
		t.Errorf("expected ErrProtocol, got %s", aErr.Kind)
	}
}
