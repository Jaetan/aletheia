// SPDX-FileCopyrightText: 2025 Nicolas Pelletier
// SPDX-License-Identifier: BSD-2-Clause

package aletheia_test

import (
	"errors"
	"fmt"
	"slices"
	"testing"

	"github.com/aletheia-automotive/aletheia-go/v5/aletheia"
)

// errorEnvelope is an error response carrying the code and message.
func errorEnvelope(code, msg string) aletheia.MockResponse {
	return aletheia.Respond(fmt.Sprintf(`{"status":"error","code":%q,"message":%q}`, code, msg))
}

// A coded error envelope reaches the caller as an *aletheia.Error of protocol
// kind carrying the kernel's code, on the JSON route and on the binary one.
// The four geometry codes are the refusals of the kernel's shared entry gate
// (geometryRefusal in src/Aletheia/DBC/Decidable/SignalGeometry.agda), which
// measures the submitted values against the frame: a bit length of zero, a
// start bit outside the frame, a bit length past it, and, for a big-endian
// signal, a descending run that wraps past the end. The gate itself is
// exercised against the real library by the C++ and Python tests and by the
// cross-binding test here; these rows are this binding's decode of what it
// emits.
func TestCodedErrorEnvelopesReachTheCaller(t *testing.T) {
	parseDBC := func(c *aletheia.Client) error { _, err := c.ParseDBC(ctx, testDBC()); return err }
	formatDBC := func(c *aletheia.Client) error { _, err := c.FormatDBC(ctx); return err }
	cases := map[string]struct {
		code string
		msg  string
		call func(*aletheia.Client) error
	}{
		"no DBC loaded":            {aletheia.CodeHandlerNoDBC, "no DBC loaded", formatDBC},
		"bit length zero":          {aletheia.CodeParseSignalBitLengthZero, "signal bit length must be at least 1", parseDBC},
		"start bit past the frame": {aletheia.CodeParseSignalStartBitExceedsFrame, "signal start bit 100 is outside the frame (8 bytes = 64 bits)", parseDBC},
		"big-endian run wraps":     {aletheia.CodeParseSignalBigEndianOverflow, "big-endian signal at start bit 62 with length 8 runs past the end of the frame (8 bytes)", parseDBC},
		"non-terminating rational": {aletheia.CodeParseNonTerminatingRational, "rational field 'initial' has no terminating decimal expansion", parseDBC},
		"non-integer mux value":    {aletheia.CodeParseNonIntegerMultiplexValue, "non-integer value in 'multiplex_values' array", parseDBC},
	}
	for name, tc := range cases {
		t.Run(name, func(t *testing.T) {
			c, _ := mockClient(t, errorEnvelope(tc.code, tc.msg))
			err := tc.call(c)
			requireKind(t, err, aletheia.ErrProtocol)
			var aErr *aletheia.Error
			if !errors.As(err, &aErr) {
				t.Fatalf("expected *aletheia.Error, got %T", err)
			}
			if aErr.Code != tc.code {
				t.Errorf("Code = %q, want %q", aErr.Code, tc.code)
			}
			if aErr.Message != tc.msg {
				t.Errorf("Message = %q, want %q", aErr.Message, tc.msg)
			}
		})
	}
}

// An error the backend itself returns, which carries no envelope, reaches the
// caller rather than being swallowed.
func TestBackendError(t *testing.T) {
	c, _ := mockClient(t, aletheia.RespondErr(aletheia.NewMockError("connection lost")))
	if _, err := c.ParseDBC(ctx, testDBC()); err == nil {
		t.Fatal("expected the backend's error to reach the caller")
	}
}

// Close is idempotent and a call after it is a state error rather than a
// crash.
func TestClosedClient(t *testing.T) {
	c, err := aletheia.NewClient(aletheia.NewMockBackend(aletheia.Respond(`{"status":"success"}`)))
	if err != nil {
		t.Fatal(err)
	}
	if err := c.Close(); err != nil {
		t.Errorf("first close: %v", err)
	}
	if err := c.Close(); err != nil {
		t.Errorf("second close: %v", err)
	}
	_, err = c.ParseDBC(ctx, testDBC())
	requireKind(t, err, aletheia.ErrState)
}

// Each error kind renders as its name, and one outside the set as its value.
func TestErrorKindString(t *testing.T) {
	cases := map[aletheia.ErrorKind]string{
		aletheia.ErrProtocol:   "protocol",
		aletheia.ErrValidation: "validation",
		aletheia.ErrState:      "state",
		aletheia.ErrFFI:        "ffi",
		aletheia.ErrorKind(99): "ErrorKind(99)",
	}
	for kind, want := range cases {
		if got := kind.String(); got != want {
			t.Errorf("ErrorKind(%d).String() = %q, want %q", kind, got, want)
		}
	}
}

// An error carrying a cause renders both parts and unwraps to it, so
// errors.Is reaches the cause; one with no cause renders one part and
// unwraps to nil.
func TestError_CauseIsRenderedAndUnwrapped(t *testing.T) {
	cause := errors.New("underlying")
	wrapped := aletheia.WrapValidationError("could not load", cause)
	if got, want := wrapped.Error(), "aletheia validation error: could not load: underlying"; got != want {
		t.Errorf("Error() = %q, want %q", got, want)
	}
	if !errors.Is(wrapped, cause) {
		t.Error("errors.Is must reach the cause through Unwrap")
	}
	bare := aletheia.NewValidationError("no cause")
	if got, want := bare.Error(), "aletheia validation error: no cause"; got != want {
		t.Errorf("Error() = %q, want %q", got, want)
	}
	if errors.Unwrap(bare) != nil {
		t.Error("an error with no cause must unwrap to nil")
	}
}

// An exhausted mock queue is a misconfigured test, so the mock answers a
// state error naming the operation it starved on rather than inventing a
// response; the starved call is recorded first, so the inputs still show it,
// and a queued response still takes priority until the queue drains again.
// The C++, Python and Rust mocks refuse the same way.
func TestMockBackend_ErrorsOnQueueExhaustion(t *testing.T) {
	wantStateError := func(t *testing.T, err error, wantMsg string) {
		t.Helper()
		requireKind(t, err, aletheia.ErrState)
		var aErr *aletheia.Error
		if errors.As(err, &aErr) && aErr.Message != wantMsg {
			t.Errorf("Message = %q, want %q", aErr.Message, wantMsg)
		}
	}

	empty := aletheia.NewMockBackend()
	state, err := empty.Init()
	if err != nil {
		t.Fatal(err)
	}

	jsonCmd := `{"command":"setProperties","formulas":[]}`
	_, err = empty.Process(state, jsonCmd)
	wantStateError(t, err, "mock backend: no queued response for process")

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

	inputs := empty.Inputs()
	if !slices.Contains(inputs, jsonCmd) {
		t.Errorf("Inputs() = %q, want the starved JSON input %q", inputs, jsonCmd)
	}
	if !slices.Contains(inputs, "<binary:sendFrame>") {
		t.Errorf("Inputs() = %q, want the starved binary sentinel", inputs)
	}

	primed := aletheia.NewMockBackend(aletheia.Respond(`{"custom":true}`))
	pState, err := primed.Init()
	if err != nil {
		t.Fatal(err)
	}
	got, err := primed.Process(pState, jsonCmd)
	if err != nil {
		t.Fatalf("a queued response must not error: %v", err)
	}
	if got != `{"custom":true}` {
		t.Errorf("Process = %q, want the queued response", got)
	}
	_, err = primed.Process(pState, jsonCmd)
	wantStateError(t, err, "mock backend: no queued response for process")
}
