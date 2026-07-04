// SPDX-FileCopyrightText: 2025 Nicolas Pelletier
// SPDX-License-Identifier: BSD-2-Clause

package aletheia

import (
	"errors"
	"strings"
	"testing"
)

// These tests pin the reject branches of the error-response decoders
// (checkErrorStatus → requireString + inputBoundExceededFromResponse) that the
// happy-path integration tests never reach. Each drives the *pure* decoder entry
// parseSuccessResponse with a crafted wire string — no FFI/RTS — so a boundary or
// condition mutation on these arms has a killing test.

// TestRequireString_RejectsErrorEnvelope covers requireString's two reject
// branches (field absent, field present-but-non-string) via a status="error"
// response whose "code" field is missing or ill-typed. The Agda core guarantees
// both code and message are present strings, so a violation signals FFI drift and
// must surface as a protocol error rather than being papered over with a default.
func TestRequireString_RejectsErrorEnvelope(t *testing.T) {
	cases := map[string]string{
		"missing code":    `{"status":"error","message":"boom"}`,
		"non-string code": `{"status":"error","code":123,"message":"boom"}`,
	}
	for name, raw := range cases {
		t.Run(name, func(t *testing.T) {
			err := parseSuccessResponse(raw)
			if err == nil {
				t.Fatalf("expected a protocol error for %s, got nil", name)
			}
			var aErr *Error
			if !errors.As(err, &aErr) || aErr.Kind != ErrProtocol {
				t.Errorf("expected an ErrProtocol *Error for %s, got %v", name, err)
			}
			if !strings.Contains(err.Error(), "code") {
				t.Errorf("error should name the offending 'code' field, got %q", err.Error())
			}
		})
	}
}

// TestValidationFailed_WellFormedEnvelopeLifts pins the lift of a
// handler_validation_failed envelope carrying the structured has_errors/issues
// payload into a typed *ValidationFailedError: both issues decode with the exact
// validation-response element shape (severity/code/detail), has_errors is decoded
// (not assumed), and Error() renders byte-identically to the generic coded error
// the lift replaces, so non-validate consumers see an unchanged message.
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
		t.Error("HasErrors = false, want true (decoded from the wire)")
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
		t.Errorf("Issues[0] = %+v, want severity error / code duplicate_signal_name", vfe.Issues[0])
	}
	if vfe.Issues[1].Severity != SeverityWarning || vfe.Issues[1].Code != IssueOffsetScaleRange {
		t.Errorf("Issues[1] = %+v, want severity warning / code offset_scale_range", vfe.Issues[1])
	}
	if vfe.Issues[0].Detail != "Message 'M': duplicate signal name 'S'" {
		t.Errorf("Issues[0].Detail = %q, want the wire detail", vfe.Issues[0].Detail)
	}
	if want := "aletheia protocol error: " + msg; err.Error() != want {
		t.Errorf("Error() = %q, want byte-identical generic render %q", err.Error(), want)
	}
}

// TestValidationFailed_MalformedPayloadDegrades covers the nil-return arms of
// validationFailedFromResponse: a missing or ill-typed has_errors, a missing or
// non-array issues field, and an issues array whose elements fail parseIssueArray
// (non-object element, unknown severity). Each degrades to the generic coded
// error carrying handler_validation_failed — asserting the error does NOT lift
// proves the reject branch fired, and the decode never fails harder than before.
func TestValidationFailed_MalformedPayloadDegrades(t *testing.T) {
	const prefix = `{"status":"error","code":"handler_validation_failed","message":"boom"`
	cases := map[string]string{
		"missing has_errors":  prefix + `,"issues":[]}`,
		"non-bool has_errors": prefix + `,"has_errors":"yes","issues":[]}`,
		"missing issues":      prefix + `,"has_errors":true}`,
		"non-array issues":    prefix + `,"has_errors":true,"issues":{}}`,
		"non-object issue":    prefix + `,"has_errors":true,"issues":[42]}`,
		"unknown severity":    prefix + `,"has_errors":true,"issues":[{"severity":"fatal","code":"x","detail":"d"}]}`,
	}
	for name, raw := range cases {
		t.Run(name, func(t *testing.T) {
			err := parseSuccessResponse(raw)
			if err == nil {
				t.Fatalf("expected a coded error for %s, got nil", name)
			}
			var vfe *ValidationFailedError
			if errors.As(err, &vfe) {
				t.Errorf("malformed payload must NOT lift to *ValidationFailedError, got %v", vfe)
			}
			var aErr *Error
			if !errors.As(err, &aErr) || aErr.Kind != ErrProtocol {
				t.Fatalf("expected the degraded error to be an ErrProtocol *Error, got %v", err)
			}
			// Pin the intended path: the degrade keeps the handler_validation_failed
			// code and legacy message — NOT the generic "unexpected status"
			// fallthrough (whose Code is empty).
			if aErr.Code != CodeHandlerValidationFailed {
				t.Errorf("degraded error Code = %q, want %q", aErr.Code, CodeHandlerValidationFailed)
			}
			if aErr.Message != "boom" {
				t.Errorf("degraded error Message = %q, want %q", aErr.Message, "boom")
			}
		})
	}
}

// TestInputBoundExceeded_MalformedTripleDegrades covers the three nil-return arms
// of inputBoundExceededFromResponse: an ill-typed bound_kind, observed, or limit.
// When the code is input_bound_exceeded but the structured triple is malformed,
// the lift returns nil and checkErrorStatus degrades to a generic coded protocol
// error instead of a typed *InputBoundExceededError — asserting the error does NOT
// lift proves the reject branch fired. The "observed" case also exercises
// jsonNumberToUint64's non-json.Number default arm (a string is not a uint64).
func TestInputBoundExceeded_MalformedTripleDegrades(t *testing.T) {
	cases := map[string]string{
		"non-string bound_kind": `{"status":"error","code":"input_bound_exceeded","message":"boom","bound_kind":123,"observed":1,"limit":2}`,
		"non-number observed":   `{"status":"error","code":"input_bound_exceeded","message":"boom","bound_kind":"NestingDepth","observed":"x","limit":2}`,
		"non-number limit":      `{"status":"error","code":"input_bound_exceeded","message":"boom","bound_kind":"NestingDepth","observed":1,"limit":"x"}`,
	}
	for name, raw := range cases {
		t.Run(name, func(t *testing.T) {
			err := parseSuccessResponse(raw)
			if err == nil {
				t.Fatalf("expected a coded error for %s, got nil", name)
			}
			var bex *InputBoundExceededError
			if errors.As(err, &bex) {
				t.Errorf("malformed triple must NOT lift to *InputBoundExceededError, got %v", bex)
			}
			var aErr *Error
			if !errors.As(err, &aErr) || aErr.Kind != ErrProtocol {
				t.Fatalf("expected the degraded error to be an ErrProtocol *Error, got %v", err)
			}
			// Pin the intended path: checkErrorStatus degrades a malformed triple to a
			// coded error carrying the input_bound_exceeded code — NOT the generic
			// "unexpected status" fallthrough (whose Code is empty). This distinguishes
			// the degrade-for-this-code path from any other ErrProtocol.
			if aErr.Code != CodeInputBoundExceeded {
				t.Errorf("degraded error Code = %q, want %q", aErr.Code, CodeInputBoundExceeded)
			}
		})
	}
}
