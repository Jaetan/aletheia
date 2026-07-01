// SPDX-FileCopyrightText: 2025 Nicolas Pelletier
// SPDX-License-Identifier: BSD-2-Clause

package aletheia

import (
	"encoding/json"
	"strings"
	"testing"
)

// 9007199254740993 is 2^53 + 1 — the smallest positive integer a float64 cannot
// represent (it rounds to 2^53 = ...992). These tests feed it through the *real*
// parseResponse decode path (a raw JSON string, not a hand-built map) so the
// UseNumber decoder is genuinely exercised: a json.Unmarshal-based decode would
// round it, the json.Number path keeps it exact.
const beyondFloat64Mantissa = int64(9007199254740993)

// TestParseResponse_ExactLargeRational pins the B6c precision fix at the wire
// boundary: a rational numerator above 2^53 survives parseResponse → parseRational
// exactly, in both the {numerator,denominator} object and the bare-scalar (n/1)
// shapes.
func TestParseResponse_ExactLargeRational(t *testing.T) {
	t.Run("object", func(t *testing.T) {
		m, err := parseResponse(`{"value":{"numerator":9007199254740993,"denominator":1}}`)
		if err != nil {
			t.Fatalf("parseResponse: %v", err)
		}
		r, err := parseRational(m["value"])
		if err != nil {
			t.Fatalf("parseRational: %v", err)
		}
		if r.Numerator != beyondFloat64Mantissa {
			t.Errorf("numerator: got %d, want %d (precision lost via float64?)", r.Numerator, beyondFloat64Mantissa)
		}
		if r.Denominator != 1 {
			t.Errorf("denominator: got %d, want 1", r.Denominator)
		}
	})
	t.Run("scalar", func(t *testing.T) {
		m, err := parseResponse(`{"value":9007199254740993}`)
		if err != nil {
			t.Fatalf("parseResponse: %v", err)
		}
		r, err := parseRational(m["value"])
		if err != nil {
			t.Fatalf("parseRational: %v", err)
		}
		if r.Numerator != beyondFloat64Mantissa || r.Denominator != 1 {
			t.Errorf("scalar: got %d/%d, want %d/1", r.Numerator, r.Denominator, beyondFloat64Mantissa)
		}
	})
}

// TestParseResponse_ExactLargeInt covers parseNumberAsInt64 for a value above
// 2^53 read from the real decode path.
func TestParseResponse_ExactLargeInt(t *testing.T) {
	m, err := parseResponse(`{"count":9007199254740993}`)
	if err != nil {
		t.Fatalf("parseResponse: %v", err)
	}
	n, err := parseNumberAsInt64(m["count"])
	if err != nil {
		t.Fatalf("parseNumberAsInt64: %v", err)
	}
	if n != beyondFloat64Mantissa {
		t.Errorf("got %d, want %d (precision lost via float64?)", n, beyondFloat64Mantissa)
	}
}

// TestJSONNumberToUint64_ExactLarge covers the json.Number arm for a value that
// exceeds both int64 and the float64 mantissa (2^63 + 1) — the observed/limit
// diagnostic fields can carry the full uint64 range.
func TestJSONNumberToUint64_ExactLarge(t *testing.T) {
	got, ok := jsonNumberToUint64(json.Number("9223372036854775809")) // 2^63 + 1
	if !ok {
		t.Fatal("jsonNumberToUint64 rejected a valid uint64")
	}
	if got != 9223372036854775809 {
		t.Errorf("got %d, want 9223372036854775809 (precision lost?)", got)
	}
}

// TestJSONNumberToUint64_Rejects pins the err branch: a non-integer or negative
// json.Number is not a uint64.
func TestJSONNumberToUint64_Rejects(t *testing.T) {
	for _, s := range []string{"1.5", "-1", "1e3", "nope"} {
		if _, ok := jsonNumberToUint64(json.Number(s)); ok {
			t.Errorf("jsonNumberToUint64(%q): expected rejection, got ok", s)
		}
	}
}

// TestParseResponse_RejectsTrailingData preserves the trailing-byte rejection
// json.Unmarshal gave us but a bare Decoder drops: a response must be exactly one
// JSON value. Trailing whitespace stays valid.
func TestParseResponse_RejectsTrailingData(t *testing.T) {
	// A successfully-decoded second value → "unexpected trailing data".
	for _, raw := range []string{`{"a":1}{"b":2}`, `{"a":1} 7`} {
		_, err := parseResponse(raw)
		if err == nil || !strings.Contains(err.Error(), "unexpected trailing data") {
			t.Errorf("parseResponse(%q): want 'unexpected trailing data', got %v", raw, err)
		}
	}
	// Malformed trailing bytes → wrapped decoder error (preserves the cause).
	if _, err := parseResponse(`{"a":1}garbage`); err == nil ||
		!strings.Contains(err.Error(), "invalid trailing data") {
		t.Errorf("parseResponse(malformed trailing): want 'invalid trailing data', got %v", err)
	}
	// A single value with trailing whitespace stays valid.
	if _, err := parseResponse("{\"a\":1}\n  \t"); err != nil {
		t.Errorf("trailing whitespace must be accepted: %v", err)
	}
}

// TestParseRational_RejectsBadComponents confirms the json.Number decode path
// rejects every adversarial wire form: a fractional or out-of-range scalar, a
// fractional/out-of-range numerator or denominator in the dict form, a dict
// missing the numerator or denominator field, and a zero/negative denominator.
// This is the production path (parseResponse → json.Number); a native Go float64
// is not a reachable decoder input.
func TestParseRational_RejectsBadComponents(t *testing.T) {
	cases := map[string]string{
		"fractional scalar":        `{"v":1.5}`,
		"out-of-range scalar":      `{"v":99999999999999999999}`,
		"fractional numerator":     `{"v":{"numerator":1.5,"denominator":2}}`,
		"fractional denom":         `{"v":{"numerator":1,"denominator":0.5}}`,
		"zero denominator":         `{"v":{"numerator":1,"denominator":0}}`,
		"negative denominator":     `{"v":{"numerator":1,"denominator":-2}}`,
		"out-of-range numerator":   `{"v":{"numerator":99999999999999999999,"denominator":1}}`,
		"out-of-range denominator": `{"v":{"numerator":1,"denominator":99999999999999999999}}`,
		"missing numerator":        `{"v":{"denominator":2}}`,
		"missing denominator":      `{"v":{"numerator":1}}`,
	}
	for name, raw := range cases {
		t.Run(name, func(t *testing.T) {
			m, err := parseResponse(raw)
			if err != nil {
				t.Fatalf("parseResponse: %v", err)
			}
			if _, err := parseRational(m["v"]); err == nil {
				t.Errorf("expected rejection for %s", name)
			}
		})
	}
}

// TestParseNumberAsInt64_Rejects pins parseNumberAsInt64's reject branches on the
// json.Number path: the scalar forms (fractional, out-of-range, non-number) and
// the dict forms (missing field, fractional component, out-of-range component,
// non-exact rational, zero denominator), so a boundary/condition mutation on any
// arm has a killing test.
func TestParseNumberAsInt64_Rejects(t *testing.T) {
	cases := map[string]string{
		"fractional scalar":             `{"v":2.5}`,
		"non-exact rational":            `{"v":{"numerator":3,"denominator":2}}`,
		"zero denominator":              `{"v":{"numerator":4,"denominator":0}}`,
		"out-of-range scalar":           `{"v":99999999999999999999}`,
		"non-number":                    `{"v":"nope"}`,
		"missing field (dict)":          `{"v":{"denominator":2}}`,
		"fractional numerator (dict)":   `{"v":{"numerator":1.5,"denominator":2}}`,
		"out-of-range numerator (dict)": `{"v":{"numerator":99999999999999999999,"denominator":1}}`,
	}
	for name, raw := range cases {
		t.Run(name, func(t *testing.T) {
			m, err := parseResponse(raw)
			if err != nil {
				t.Fatalf("parseResponse: %v", err)
			}
			if _, err := parseNumberAsInt64(m["v"]); err == nil {
				t.Errorf("expected rejection for %s", name)
			}
		})
	}
}

// TestParseNumberAsInt64_AcceptsExactRational is the positive boundary for the
// num%den==0 reduce path (6/2 = 3); paired with the "non-exact rational" reject
// above, it pins both sides of the divisibility check.
func TestParseNumberAsInt64_AcceptsExactRational(t *testing.T) {
	m, err := parseResponse(`{"v":{"numerator":6,"denominator":2}}`)
	if err != nil {
		t.Fatalf("parseResponse: %v", err)
	}
	got, err := parseNumberAsInt64(m["v"])
	if err != nil {
		t.Fatalf("parseNumberAsInt64: %v", err)
	}
	if got != 3 {
		t.Errorf("got %d, want 3", got)
	}
}
