// SPDX-FileCopyrightText: 2025 Nicolas Pelletier
// SPDX-License-Identifier: BSD-2-Clause

package aletheia

import (
	"errors"
	"strings"
	"testing"
)

// The refusal side of the response decoders, over crafted wire text. Nothing
// here reaches the library: an error envelope is decoded by the same pure
// entry a success is, so every reject arm has a case, which the tests driving
// real traffic never reach.

// requireDegradedCoded holds that a refusal the decoder could not lift is
// still the generic coded error, carrying the kernel's own code and message. A
// caller reading either sees what it would have seen before any lift existed,
// and the decode never fails harder than that.
func requireDegradedCoded(t *testing.T, err error, code, message string) {
	t.Helper()
	if err == nil {
		t.Fatal("expected a coded error, got nil")
	}
	var aErr *Error
	if !errors.As(err, &aErr) {
		t.Fatalf("expected *Error, got %T: %v", err, err)
	}
	if aErr.Kind != ErrProtocol {
		t.Errorf("Kind = %v, want ErrProtocol", aErr.Kind)
	}
	if aErr.Code != code {
		t.Errorf("Code = %q, want %q: the refusal must keep its own code rather than fall through", aErr.Code, code)
	}
	if aErr.Message != message {
		t.Errorf("Message = %q, want %q", aErr.Message, message)
	}
}

// An error envelope must name its code and its message, both as strings. The
// kernel writes both, so a missing or ill-typed one is drift between the
// binding and the kernel, which a default would hide.
func TestRequireString_RejectsErrorEnvelope(t *testing.T) {
	cases := map[string]string{
		"missing code":    `{"status":"error","message":"boom"}`,
		"non-string code": `{"status":"error","code":123,"message":"boom"}`,
	}
	for name, raw := range cases {
		t.Run(name, func(t *testing.T) {
			err := parseSuccessResponse(raw)
			if err == nil {
				t.Fatal("expected a protocol error, got nil")
			}
			var aErr *Error
			if !errors.As(err, &aErr) || aErr.Kind != ErrProtocol {
				t.Errorf("expected an ErrProtocol *Error, got %v", err)
			}
			if !strings.Contains(err.Error(), "code") {
				t.Errorf("error %q does not name the field at fault", err)
			}
		})
	}
}

// A refusal of a DBC that failed validation lifts to the typed error: both
// issues arrive with their severity, code and detail, the error flag is read
// off the wire rather than assumed, and the rendered message is what the
// generic coded error rendered, so a caller that only reads it sees no change.
func TestValidationFailed_WellFormedEnvelopeLifts(t *testing.T) {
	const msg = "ParseDBCText: validation failed: Message 'M': duplicate signal name 'S'"
	raw := `{"status":"error","code":"handler_validation_failed",` +
		`"message":"` + msg + `","has_errors":true,"issues":[` +
		`{"severity":"error","code":"duplicate_signal_name","detail":"Message 'M': duplicate signal name 'S'"},` +
		`{"severity":"warning","code":"offset_scale_range","detail":"Signal 'S': offset/scale range suspicious"}]}`
	err := parseSuccessResponse(raw)
	if err == nil {
		t.Fatal("expected a ValidationFailedError, got nil")
	}
	var vfe *ValidationFailedError
	if !errors.As(err, &vfe) {
		t.Fatalf("expected *ValidationFailedError, got %T: %v", err, err)
	}
	if !vfe.HasErrors {
		t.Error("HasErrors = false, want true from the wire")
	}
	if vfe.Code != CodeHandlerValidationFailed {
		t.Errorf("Code = %q, want %q", vfe.Code, CodeHandlerValidationFailed)
	}
	if vfe.Message != msg {
		t.Errorf("Message = %q, want %q", vfe.Message, msg)
	}
	if len(vfe.Issues) != 2 {
		t.Fatalf("len(Issues) = %d, want 2", len(vfe.Issues))
	}
	if vfe.Issues[0].Severity != SeverityError || vfe.Issues[0].Code != IssueDuplicateSignalName {
		t.Errorf("Issues[0] = %+v, want error / duplicate_signal_name", vfe.Issues[0])
	}
	if vfe.Issues[1].Severity != SeverityWarning || vfe.Issues[1].Code != IssueOffsetScaleRange {
		t.Errorf("Issues[1] = %+v, want warning / offset_scale_range", vfe.Issues[1])
	}
	if vfe.Issues[0].Detail != "Message 'M': duplicate signal name 'S'" {
		t.Errorf("Issues[0].Detail = %q, want the wire detail", vfe.Issues[0].Detail)
	}
	if want := "aletheia protocol error: " + msg; err.Error() != want {
		t.Errorf("Error() = %q, want the generic render %q", err.Error(), want)
	}
}

// The two refusals that carry an issues payload lift only when the payload is
// whole. Each malformed shape leaves the generic coded error instead, and the
// two refusals are held to the same six shapes, their decoders being the same
// shape themselves.
func TestIssueBearingRefusals_MalformedPayloadDegrades(t *testing.T) {
	shapes := func(code string) map[string]string {
		prefix := `{"status":"error","code":"` + code + `","message":"boom"`
		return map[string]string{
			"missing has_errors":  prefix + `,"issues":[]}`,
			"non-bool has_errors": prefix + `,"has_errors":"yes","issues":[]}`,
			"missing issues":      prefix + `,"has_errors":true}`,
			"non-array issues":    prefix + `,"has_errors":true,"issues":{}}`,
			"non-object issue":    prefix + `,"has_errors":true,"issues":[42]}`,
			"unknown severity":    prefix + `,"has_errors":true,"issues":[{"severity":"fatal","code":"x","detail":"d"}]}`,
		}
	}
	refusals := map[string]struct {
		code   string
		lifted func(error) bool
	}{
		"validation failed": {CodeHandlerValidationFailed, func(err error) bool {
			var e *ValidationFailedError
			return errors.As(err, &e)
		}},
		"text round trip failed": {CodeHandlerTextRoundtripFailed, func(err error) bool {
			var e *TextRoundTripFailedError
			return errors.As(err, &e)
		}},
	}
	for refusal, tc := range refusals {
		t.Run(refusal, func(t *testing.T) {
			for shape, raw := range shapes(tc.code) {
				t.Run(shape, func(t *testing.T) {
					err := parseSuccessResponse(raw)
					if tc.lifted(err) {
						t.Errorf("a malformed payload lifted to the typed error: %v", err)
					}
					requireDegradedCoded(t, err, tc.code, "boom")
				})
			}
		})
	}
}

// A bound refusal lifts only with all three of its numbers well formed. The
// case with a string where a size belongs also drives the arm that refuses a
// value that is not a wire number at all.
func TestInputBoundExceeded_MalformedTripleDegrades(t *testing.T) {
	cases := map[string]string{
		"non-string bound_kind": `{"status":"error","code":"input_bound_exceeded","message":"boom","bound_kind":123,"observed":1,"limit":2}`,
		"non-number observed":   `{"status":"error","code":"input_bound_exceeded","message":"boom","bound_kind":"NestingDepth","observed":"x","limit":2}`,
		"non-number limit":      `{"status":"error","code":"input_bound_exceeded","message":"boom","bound_kind":"NestingDepth","observed":1,"limit":"x"}`,
	}
	for name, raw := range cases {
		t.Run(name, func(t *testing.T) {
			err := parseSuccessResponse(raw)
			var bex *InputBoundExceededError
			if errors.As(err, &bex) {
				t.Errorf("a malformed triple lifted to the typed error: %v", bex)
			}
			requireDegradedCoded(t, err, CodeInputBoundExceeded, "boom")
		})
	}
}
