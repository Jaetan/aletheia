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
				t.Errorf("expected the degraded error to be an ErrProtocol *Error, got %v", err)
			}
		})
	}
}
