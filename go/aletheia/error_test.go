// SPDX-FileCopyrightText: 2025 Nicolas Pelletier
// SPDX-License-Identifier: BSD-2-Clause

package aletheia_test

import (
	"errors"
	"fmt"
	"slices"
	"testing"

	"github.com/Jaetan/aletheia/go/v5/aletheia"
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
	ctx := t.Context()
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
	ctx := t.Context()
	c, _ := mockClient(t, aletheia.RespondErr(aletheia.NewMockError("connection lost")))
	if _, err := c.ParseDBC(ctx, testDBC()); err == nil {
		t.Fatal("expected the backend's error to reach the caller")
	}
}

// Close is idempotent and a call after it is a state error rather than a
// crash.
func TestClosedClient(t *testing.T) {
	ctx := t.Context()
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

// An error prints its message alone, the kernel's text when the kernel
// refused; one carrying a cause prints the cause after it, as Go wraps
// context, and unwraps to it, so errors.Is reaches the cause; one with no
// cause unwraps to nil.
func TestError_CauseIsRenderedAndUnwrapped(t *testing.T) {
	cause := errors.New("underlying")
	wrapped := aletheia.WrapValidationError("could not load", cause)
	if got, want := wrapped.Error(), "could not load: underlying"; got != want {
		t.Errorf("Error() = %q, want %q", got, want)
	}
	if !errors.Is(wrapped, cause) {
		t.Error("errors.Is must reach the cause through Unwrap")
	}
	bare := aletheia.NewValidationError("no cause")
	if got, want := bare.Error(), "no cause"; got != want {
		t.Errorf("Error() = %q, want %q", got, want)
	}
	if errors.Unwrap(bare) != nil {
		t.Error("an error with no cause must unwrap to nil")
	}
}

// An error a loader located prints its location and its key before what it
// prints unlocated, the message with the cause after it, or the bound error's
// message or its own text; an error with no location prints that alone.
func TestError_LocationLeadsTheText(t *testing.T) {
	const parseFailure = "parse failed at line 1, column 1"
	const bound = "decimal: rational component magnitude 9223372036854775808 exceeds limit 9223372036854775807"
	coded := func(location, key string) *aletheia.Error {
		return &aletheia.Error{Kind: aletheia.ErrValidation, Code: aletheia.CodeTextParseFailure,
			Message: parseFailure, Location: location, Key: key}
	}
	kernelBound := func(location, key string) *aletheia.InputBoundExceededError {
		return &aletheia.InputBoundExceededError{BoundKind: aletheia.BoundKindRationalComponentMagnitude,
			Observed: 9223372036854775808, Limit: 9223372036854775807, Code: aletheia.CodeInputBoundExceeded,
			Field: "decimal", Message: bound, Location: location, Key: key}
	}
	bindingBound := func(location, key string) *aletheia.InputBoundExceededError {
		return &aletheia.InputBoundExceededError{BoundKind: aletheia.BoundKindRationalComponentMagnitude,
			Observed: 10, Limit: 5, Code: aletheia.CodeInputBoundExceeded, Location: location, Key: key}
	}
	cases := map[string]struct {
		err  error
		want string
	}{
		"a coded error":          {coded("", ""), parseFailure},
		"a coded error, located": {coded("Check 'C'", "value"), "Check 'C': invalid 'value': " + parseFailure},
		"an error with a cause":  {&aletheia.Error{Message: "m", Cause: errors.New("c")}, "m: c"},
		"a cause, located":       {&aletheia.Error{Message: "m", Cause: errors.New("c"), Location: "Row 2", Key: "Factor"}, "Row 2: invalid 'Factor': m: c"},
		"the kernel's bound":     {kernelBound("", ""), bound},
		"the kernel's, located":  {kernelBound("Row 2", "Value"), "Row 2: invalid 'Value': " + bound},
		"the binding's bound":    {bindingBound("", ""), "rational_component_magnitude 10 exceeds limit 5"},
		"the binding's, located": {bindingBound("Check 'C'", "value"), "Check 'C': invalid 'value': rational_component_magnitude 10 exceeds limit 5"},
	}
	for name, tc := range cases {
		t.Run(name, func(t *testing.T) {
			if got := tc.err.Error(); got != tc.want {
				t.Errorf("%s: Error() = %q, want %q", name, got, tc.want)
			}
		})
	}
}

// Locate answers a copy of a coded error or of the bound error carrying the
// location and the key, every field the kernel filled unchanged and the error
// it was given left as it was; an error with no code and one from outside the
// package come back as they were given.
func TestLocate(t *testing.T) {
	coded := &aletheia.Error{Kind: aletheia.ErrValidation, Code: aletheia.CodeTextTrailingInput,
		Message: "parse failed at line 1, column 4", Cause: errors.New("c")}
	var gotCoded *aletheia.Error
	if !errors.As(aletheia.Locate(coded, "Check 'C'", "value"), &gotCoded) {
		t.Fatal("a located coded error is not an *aletheia.Error")
	}
	wantCoded := *coded
	wantCoded.Location, wantCoded.Key = "Check 'C'", "value"
	if *gotCoded != wantCoded {
		t.Errorf("Locate(coded) = %+v, want %+v", *gotCoded, wantCoded)
	}
	if gotCoded == coded || coded.Location != "" || coded.Key != "" {
		t.Error("Locate changed the coded error it was given rather than answering a copy")
	}

	bound := &aletheia.InputBoundExceededError{BoundKind: aletheia.BoundKindRationalComponentMagnitude,
		Observed: 18446744073709551615, Limit: 9223372036854775807, Code: aletheia.CodeInputBoundExceeded,
		Field: "decimal", Message: "decimal: rational component magnitude at least 18446744073709551615 exceeds limit 9223372036854775807"}
	var gotBound *aletheia.InputBoundExceededError
	if !errors.As(aletheia.Locate(bound, "Row 2", "Factor"), &gotBound) {
		t.Fatal("a located bound error is not an *aletheia.InputBoundExceededError")
	}
	wantBound := *bound
	wantBound.Location, wantBound.Key = "Row 2", "Factor"
	if *gotBound != wantBound {
		t.Errorf("Locate(bound) = %+v, want %+v", *gotBound, wantBound)
	}
	if gotBound == bound || bound.Location != "" || bound.Key != "" {
		t.Error("Locate changed the bound error it was given rather than answering a copy")
	}

	codeless := aletheia.NewValidationError("no code")
	if got := aletheia.Locate(codeless, "Row 2", "Value"); got != error(codeless) || codeless.Location != "" || codeless.Key != "" {
		t.Errorf("Locate(codeless) = %#v, want the error it was given, unchanged", got)
	}
	foreign := errors.New("not ours")
	if got := aletheia.Locate(foreign, "Row 2", "Value"); got != foreign {
		t.Errorf("Locate(foreign) = %#v, want the error it was given", got)
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
