// SPDX-FileCopyrightText: 2025 Nicolas Pelletier
// SPDX-License-Identifier: BSD-2-Clause

package aletheia

import (
	"encoding/json"
	"strings"
	"testing"
)

// Numbers cross the wire exactly. Every case here goes through the real decode
// entry, from a raw response rather than a hand-built map, so what is under
// test is the decoder the library uses: reading these through a float would
// round them, and reading them as decimal strings does not.

// beyondFloat64Mantissa is the smallest positive integer a float cannot hold,
// two to the fifty-third plus one, which rounds down to its neighbour.
const beyondFloat64Mantissa = int64(9007199254740993)

// A numerator past what a float can hold survives, in the object shape and in
// the bare scalar alike.
func TestParseResponse_ExactLargeRational(t *testing.T) {
	cases := map[string]string{
		"object": `{"value":{"numerator":9007199254740993,"denominator":1}}`,
		"scalar": `{"value":9007199254740993}`,
	}
	for name, raw := range cases {
		t.Run(name, func(t *testing.T) {
			m, err := parseResponse(raw)
			if err != nil {
				t.Fatalf("parseResponse: %v", err)
			}
			r, err := parseRational(m["value"])
			if err != nil {
				t.Fatalf("parseRational: %v", err)
			}
			if r.Numerator != beyondFloat64Mantissa || r.Denominator != 1 {
				t.Errorf("got %d/%d, want %d/1: the value went through a float", r.Numerator, r.Denominator, beyondFloat64Mantissa)
			}
		})
	}
}

// An integer past what a float can hold survives too.
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
		t.Errorf("got %d, want %d: the value went through a float", n, beyondFloat64Mantissa)
	}
}

// The sizes a bound refusal reports use the whole unsigned range, past both
// what a float holds and what a signed integer holds.
func TestJSONNumberToUint64_ExactLarge(t *testing.T) {
	got, ok := jsonNumberToUint64(json.Number("9223372036854775809")) // two to the sixty-third, plus one
	if !ok {
		t.Fatal("a valid unsigned value was refused")
	}
	if got != 9223372036854775809 {
		t.Errorf("got %d, want 9223372036854775809", got)
	}
}

// Anything that is not an unsigned integer is refused rather than coerced.
func TestJSONNumberToUint64_Rejects(t *testing.T) {
	for _, s := range []string{"1.5", "-1", "1e3", "nope"} {
		if _, ok := jsonNumberToUint64(json.Number(s)); ok {
			t.Errorf("%q was taken as an unsigned integer", s)
		}
	}
}

// A response is one JSON value. A decoder accepts what follows the first one,
// so the refusal is made by hand: a second value is trailing data, bytes that
// do not parse are a decode failure carrying its cause, and trailing space is
// neither.
func TestParseResponse_RejectsTrailingData(t *testing.T) {
	for _, raw := range []string{`{"a":1}{"b":2}`, `{"a":1} 7`} {
		_, err := parseResponse(raw)
		if err == nil || !strings.Contains(err.Error(), "unexpected trailing data") {
			t.Errorf("parseResponse(%q): want it to name the trailing data, got %v", raw, err)
		}
	}
	if _, err := parseResponse(`{"a":1}garbage`); err == nil ||
		!strings.Contains(err.Error(), "invalid trailing data") {
		t.Errorf("parseResponse with malformed trailing bytes: want it to name them, got %v", err)
	}
	if _, err := parseResponse("{\"a\":1}\n  \t"); err != nil {
		t.Errorf("trailing whitespace must be accepted: %v", err)
	}
}

// The two numeric readers share one reader for a rational's components, so
// every wire shape is put to both. Where they differ is the point: a rational
// that does not divide evenly is a value and not an integer, and the two
// columns say which reader takes which shape.
func TestNumericReaders_AcceptAndRefuseTheSameShapes(t *testing.T) {
	cases := map[string]struct {
		raw        string
		asRational bool
		asInteger  bool
	}{
		"integer scalar":            {`{"v":7}`, true, true},
		"rational that divides":     {`{"v":{"numerator":6,"denominator":2}}`, true, true},
		"rational that does not":    {`{"v":{"numerator":3,"denominator":2}}`, true, false},
		"fractional scalar":         {`{"v":1.5}`, false, false},
		"scalar past int64":         {`{"v":99999999999999999999}`, false, false},
		"not a number":              {`{"v":"nope"}`, false, false},
		"fractional numerator":      {`{"v":{"numerator":1.5,"denominator":2}}`, false, false},
		"fractional denominator":    {`{"v":{"numerator":1,"denominator":0.5}}`, false, false},
		"zero denominator":          {`{"v":{"numerator":1,"denominator":0}}`, false, false},
		"negative denominator":      {`{"v":{"numerator":1,"denominator":-2}}`, false, false},
		"numerator past int64":      {`{"v":{"numerator":99999999999999999999,"denominator":1}}`, false, false},
		"denominator past int64":    {`{"v":{"numerator":1,"denominator":99999999999999999999}}`, false, false},
		"no numerator":              {`{"v":{"denominator":2}}`, false, false},
		"no denominator":            {`{"v":{"numerator":1}}`, false, false},
		"negative over a negative":  {`{"v":{"numerator":-4,"denominator":-2}}`, false, false},
		"rational of a null value":  {`{"v":null}`, false, false},
		"rational of an array":      {`{"v":[1,2]}`, false, false},
		"denominator not a number":  {`{"v":{"numerator":1,"denominator":"2"}}`, false, false},
		"numerator not a number":    {`{"v":{"numerator":"1","denominator":2}}`, false, false},
		"rational of a bare object": {`{"v":{}}`, false, false},
	}
	for name, tc := range cases {
		t.Run(name, func(t *testing.T) {
			m, err := parseResponse(tc.raw)
			if err != nil {
				t.Fatalf("parseResponse: %v", err)
			}
			_, ratErr := parseRational(m["v"])
			if (ratErr == nil) != tc.asRational {
				t.Errorf("as a rational: error %v, want accepted = %v", ratErr, tc.asRational)
			}
			_, intErr := parseNumberAsInt64(m["v"])
			if (intErr == nil) != tc.asInteger {
				t.Errorf("as an integer: error %v, want accepted = %v", intErr, tc.asInteger)
			}
		})
	}
}

// The integer reader divides a rational that divides evenly.
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

// A negative denominator is refused on both paths, and the message says so.
// The kernel emits none, and a reader that divided by it would answer a
// positive integer for a shape every other binding refuses.
func TestNumericReaders_NameTheNegativeDenominator(t *testing.T) {
	m, err := parseResponse(`{"v":{"numerator":-4,"denominator":-2}}`)
	if err != nil {
		t.Fatalf("parseResponse: %v", err)
	}
	got, err := parseNumberAsInt64(m["v"])
	if err == nil {
		t.Fatalf("a negative denominator decoded to %d", got)
	}
	if !strings.Contains(err.Error(), "negative denominator") {
		t.Errorf("Error() = %q, want it to name the negative denominator", err)
	}
}
