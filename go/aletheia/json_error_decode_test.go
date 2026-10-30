// SPDX-FileCopyrightText: 2025 Nicolas Pelletier
// SPDX-License-Identifier: BSD-2-Clause

package aletheia

import (
	"errors"
	"slices"
	"testing"
)

// The refusal side of the response decoders, over crafted wire text. Nothing
// here reaches the library: an error envelope is decoded by the same pure
// entry a success is, so every reject arm has a case, which the tests driving
// real traffic never reach.

// requireCodedError holds that a refusal whose code no lift types is the
// generic coded error, carrying the kernel's own code and message.
func requireCodedError(t *testing.T, err error, code, message string) {
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
// binding and the kernel, which a default would hide: it is refused at its
// place. A bound refusal whose message is not a string is refused so, rather
// than lifted with no message.
func TestErrorEnvelope_RefusesACodeOrMessageNotAString(t *testing.T) {
	cases := map[string]struct{ raw, want string }{
		"missing code":    {`{"status":"error","message":"boom"}`, "reply code: expected string, got nothing"},
		"non-string code": {`{"status":"error","code":123,"message":"boom"}`, "reply code: expected string, got number"},
		"non-string bound refusal message": {
			`{"status":"error","code":"input_bound_exceeded","message":7,"bound_kind":"nesting_depth","observed":65,"limit":64}`,
			"reply message: expected string, got number",
		},
	}
	for name, tc := range cases {
		t.Run(name, func(t *testing.T) {
			requireReplyRefusal(t, parseSuccessResponse(tc.raw), tc.want)
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
	if want := msg; err.Error() != want {
		t.Errorf("Error() = %q, want the generic render %q", err.Error(), want)
	}
}

// The two refusals that carry an issues payload lift only when the payload is
// whole. Each malformed shape is refused at its place, and the two refusals
// are held to the same shapes, their decoders being the same shape
// themselves. A severity outside the two words takes the last arm, warning,
// and lifts.
func TestIssueBearingRefusals_MalformedPayloadIsRefused(t *testing.T) {
	shapes := func(code string) map[string]struct{ raw, want string } {
		prefix := `{"status":"error","code":"` + code + `","message":"boom"`
		return map[string]struct{ raw, want string }{
			"missing has_errors":  {prefix + `,"issues":[]}`, "reply has_errors: expected boolean, got nothing"},
			"non-bool has_errors": {prefix + `,"has_errors":"yes","issues":[]}`, "reply has_errors: expected boolean, got string"},
			"missing issues":      {prefix + `,"has_errors":true}`, "reply issues: expected array, got nothing"},
			"non-array issues":    {prefix + `,"has_errors":true,"issues":{}}`, "reply issues: expected array, got object"},
			"non-object issue":    {prefix + `,"has_errors":true,"issues":[42]}`, "reply issues: expected object, got number"},
		}
	}
	refusals := map[string]struct {
		code   string
		issues func(error) ([]ValidationIssue, bool)
	}{
		"validation failed": {CodeHandlerValidationFailed, func(err error) ([]ValidationIssue, bool) {
			var e *ValidationFailedError
			if !errors.As(err, &e) {
				return nil, false
			}
			return e.Issues, true
		}},
		"text round trip failed": {CodeHandlerTextRoundtripFailed, func(err error) ([]ValidationIssue, bool) {
			var e *TextRoundTripFailedError
			if !errors.As(err, &e) {
				return nil, false
			}
			return e.Issues, true
		}},
	}
	for refusal, tc := range refusals {
		t.Run(refusal, func(t *testing.T) {
			for shape, malformed := range shapes(tc.code) {
				t.Run(shape, func(t *testing.T) {
					err := parseSuccessResponse(malformed.raw)
					if _, lifted := tc.issues(err); lifted {
						t.Errorf("a malformed payload lifted to the typed error: %v", err)
					}
					requireReplyRefusal(t, err, malformed.want)
				})
			}
			t.Run("unknown severity", func(t *testing.T) {
				err := parseSuccessResponse(`{"status":"error","code":"` + tc.code + `","message":"boom",` +
					`"has_errors":true,"issues":[{"severity":"fatal","code":"x","detail":"d"}]}`)
				issues, lifted := tc.issues(err)
				want := []ValidationIssue{{Severity: SeverityWarning, Code: "x", Detail: "d"}}
				if !lifted || !slices.Equal(issues, want) {
					t.Errorf("got %v, want the typed error over %+v", err, want)
				}
			})
		})
	}
}

// A bound refusal lifts only with its kind and both of its numbers well
// formed, and with its field a string when it names one; each broken place is
// refused there, a string where a size belongs among them.
func TestInputBoundExceeded_MalformedPayloadIsRefused(t *testing.T) {
	cases := map[string]struct{ raw, want string }{
		"non-string bound_kind": {
			`{"status":"error","code":"input_bound_exceeded","message":"boom","bound_kind":123,"observed":1,"limit":2}`,
			"reply bound_kind: expected string, got number",
		},
		"non-number observed": {
			`{"status":"error","code":"input_bound_exceeded","message":"boom","bound_kind":"NestingDepth","observed":"x","limit":2}`,
			"reply observed: expected number, got string",
		},
		"non-number limit": {
			`{"status":"error","code":"input_bound_exceeded","message":"boom","bound_kind":"NestingDepth","observed":1,"limit":"x"}`,
			"reply limit: expected number, got string",
		},
		"non-string field": {
			`{"status":"error","code":"input_bound_exceeded","message":"boom","bound_kind":"array_cardinality","observed":3,"limit":2,"field":7}`,
			"reply field: expected string, got number",
		},
	}
	for name, tc := range cases {
		t.Run(name, func(t *testing.T) {
			err := parseSuccessResponse(tc.raw)
			var bex *InputBoundExceededError
			if errors.As(err, &bex) {
				t.Errorf("a malformed payload lifted to the typed error: %v", bex)
			}
			requireReplyRefusal(t, err, tc.want)
		})
	}
}

// A bound refusal lifts to the typed error carrying the kernel's message
// whole, and that message is the error's text, whether or not the refusal
// names a field.
func TestInputBoundExceeded_WellFormedEnvelopeLifts(t *testing.T) {
	cases := map[string]struct {
		payload, msg, kind, field string
		observed, limit           uint64
	}{
		"names a field": {
			payload:  `"bound_kind":"array_cardinality","observed":10001,"limit":10000,"field":"senders array"`,
			msg:      "ParseDBC: senders array: array cardinality 10001 exceeds limit 10000",
			kind:     BoundKindArrayCardinality,
			field:    "senders array",
			observed: 10001, limit: 10000,
		},
		"names none": {
			payload:  `"bound_kind":"nesting_depth","observed":65,"limit":64`,
			msg:      "nesting depth 65 exceeds limit 64",
			kind:     BoundKindNestingDepth,
			observed: 65, limit: 64,
		},
	}
	for name, tc := range cases {
		t.Run(name, func(t *testing.T) {
			raw := `{"status":"error","code":"input_bound_exceeded","message":"` + tc.msg + `",` + tc.payload + `}`
			err := parseSuccessResponse(raw)
			var bex *InputBoundExceededError
			if !errors.As(err, &bex) {
				t.Fatalf("expected *InputBoundExceededError, got %T: %v", err, err)
			}
			if bex.BoundKind != tc.kind || bex.Observed != (Uint128{Lo: tc.observed}) || bex.Limit != (Uint128{Lo: tc.limit}) || bex.Field != tc.field {
				t.Errorf("lifted %s %s / %s field %q, want %s %d / %d field %q",
					bex.BoundKind, bex.Observed, bex.Limit, bex.Field, tc.kind, tc.observed, tc.limit, tc.field)
			}
			if bex.Code != CodeInputBoundExceeded {
				t.Errorf("Code = %q, want %q", bex.Code, CodeInputBoundExceeded)
			}
			if bex.Message != tc.msg {
				t.Errorf("Message = %q, want the kernel's %q", bex.Message, tc.msg)
			}
			if got := err.Error(); got != tc.msg {
				t.Errorf("Error() = %q, want the kernel's message %q", got, tc.msg)
			}
		})
	}
}
