package aletheia_test

import (
	"errors"
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

	_, err = c.FormatDBC()
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

	_, err = c.ParseDBC(testDBC())
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

	_, err = c.ParseDBC(testDBC())
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
	_, err = c.ParseDBC(testDBC())
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
		{aletheia.ErrorKind(99), "unknown"},
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
// Parse error codes from the PhysicallyValid gate (2026-04-08)
// ---------------------------------------------------------------------------
// DBC/JSONParser.agda's physicalGate enforces three constraints on BigEndian
// signals at parse time (closes deferred item §12.1):
//
//   • bitLength ≥ 1                     → SignalBitLengthZero
//   • csb + bl − 1 < frameBytes * 8      → SignalOverflowsFrame
//   • bl − 1 ≤ csb                      → SignalMSBBelowBitLength
//
// Go's surface for this layer is JSON error-code parsing — the actual
// physicalGate logic lives in Agda and is already verified by the
// real-FFI C++/Python tests. These tests exercise the Go binding's
// JSON error-code extraction via MockBackend, ensuring the three new
// codes (from 2026-04-08) round-trip through parseErrorResponse into
// aErr.Code with the expected ErrProtocol kind.

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

	_, err = c.ParseDBC(testDBC())
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

	_, err = c.ParseDBC(testDBC())
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

	_, err = c.ParseDBC(testDBC())
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

	_, err = c.ParseDBC(testDBC())
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
