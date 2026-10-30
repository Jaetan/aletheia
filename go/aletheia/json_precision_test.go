// SPDX-FileCopyrightText: 2025 Nicolas Pelletier
// SPDX-License-Identifier: BSD-2-Clause

package aletheia

import (
	"encoding/json"
	"math"
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
	want := Rational{Numerator: Uint128{Lo: uint64(beyondFloat64Mantissa)}, Denominator: Uint128{Lo: 1}}
	for name, raw := range cases {
		t.Run(name, func(t *testing.T) {
			m, err := parseResponse(raw)
			if err != nil {
				t.Fatalf("parseResponse: %v", err)
			}
			r, err := readRational(m["value"], "value")
			if err != nil {
				t.Fatalf("readRational: %v", err)
			}
			if r != want {
				t.Errorf("got %+v, want %+v: the value went through a float", r, want)
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
	n, err := readInt64(m["count"], "count")
	if err != nil {
		t.Fatalf("readInt64: %v", err)
	}
	if n != beyondFloat64Mantissa {
		t.Errorf("got %d, want %d: the value went through a float", n, beyondFloat64Mantissa)
	}
}

// The sizes a bound refusal reports use the whole unsigned 128-bit range,
// past what a float, a signed integer and an unsigned word hold.
func TestReadUint128_ExactLarge(t *testing.T) {
	cases := map[string]Uint128{
		"9223372036854775809":                     {Lo: 9223372036854775809},
		"18446744073709551616":                    {Hi: 1},
		"340282366920938463463374607431768211455": {Hi: math.MaxUint64, Lo: math.MaxUint64},
	}
	for digits, want := range cases {
		got, err := readUint128(json.Number(digits), "observed")
		if err != nil {
			t.Errorf("%s: a valid unsigned value was refused: %v", digits, err)
			continue
		}
		if got != want {
			t.Errorf("%s: got %+v, want %+v", digits, got, want)
		}
	}
}

// Anything that is not an unsigned integer written as digits is refused
// rather than coerced, a number past 2^128-1 among them.
func TestReadUint128_Rejects(t *testing.T) {
	for _, s := range []string{"1.5", "-1", "1e3", "nope", "340282366920938463463374607431768211456"} {
		_, err := readUint128(json.Number(s), "observed")
		if want := "reply observed: expected number, got number"; err == nil || err.Error() != want {
			t.Errorf("%q: got %v, want %q", s, err, want)
		}
	}
}

// A response is one JSON value. A decoder accepts what follows the first one,
// so the refusal is made by hand: a second value and bytes that do not parse
// are refused as JSON text expected, naming the decoder's reason, and
// trailing space is neither.
func TestParseResponse_RejectsTrailingData(t *testing.T) {
	cases := map[string]string{
		`{"a":1}{"b":2}`: "reply: expected JSON text, got invalid character '{' after top-level value",
		`{"a":1} 7`:      "reply: expected JSON text, got invalid character '7' after top-level value",
		`{"a":1}garbage`: "reply: expected JSON text, got invalid character 'g' after top-level value",
	}
	for raw, want := range cases {
		if _, err := parseResponse(raw); err == nil || err.Error() != want {
			t.Errorf("parseResponse(%q): got %v, want %q", raw, err, want)
		}
	}
	if _, err := parseResponse("{\"a\":1}\n  \t"); err != nil {
		t.Errorf("trailing whitespace must be accepted: %v", err)
	}
}

// A rational place takes a number written as digits or a {numerator,
// denominator} object of two such numbers, a zero denominator read as written
// and a negative one flipping the sign; anything else is refused as a
// rational expected, naming the JSON kind that came. An integer place takes
// the digits alone, within its range.
func TestNumericReaders_AcceptAndRefuseTheSameShapes(t *testing.T) {
	cases := map[string]struct {
		raw        string
		asRational bool
		asInteger  bool
		arrival    string
	}{
		"integer scalar":            {`{"v":7}`, true, true, "number"},
		"rational that divides":     {`{"v":{"numerator":6,"denominator":2}}`, true, false, "object"},
		"rational that does not":    {`{"v":{"numerator":3,"denominator":2}}`, true, false, "object"},
		"fractional scalar":         {`{"v":1.5}`, false, false, "number"},
		"scalar past int64":         {`{"v":99999999999999999999}`, true, false, "number"},
		"scalar past 2^128-1":       {`{"v":340282366920938463463374607431768211456}`, false, false, "number"},
		"not a number":              {`{"v":"nope"}`, false, false, "string"},
		"fractional numerator":      {`{"v":{"numerator":1.5,"denominator":2}}`, false, false, "object"},
		"fractional denominator":    {`{"v":{"numerator":1,"denominator":0.5}}`, false, false, "object"},
		"zero denominator":          {`{"v":{"numerator":1,"denominator":0}}`, true, false, "object"},
		"negative denominator":      {`{"v":{"numerator":1,"denominator":-2}}`, true, false, "object"},
		"numerator past int64":      {`{"v":{"numerator":99999999999999999999,"denominator":1}}`, true, false, "object"},
		"denominator past int64":    {`{"v":{"numerator":1,"denominator":99999999999999999999}}`, true, false, "object"},
		"no numerator":              {`{"v":{"denominator":2}}`, false, false, "object"},
		"no denominator":            {`{"v":{"numerator":1}}`, false, false, "object"},
		"negative over a negative":  {`{"v":{"numerator":-4,"denominator":-2}}`, true, false, "object"},
		"rational of a null value":  {`{"v":null}`, false, false, "null"},
		"rational of an array":      {`{"v":[1,2]}`, false, false, "array"},
		"rational of a boolean":     {`{"v":true}`, false, false, "boolean"},
		"denominator not a number":  {`{"v":{"numerator":1,"denominator":"2"}}`, false, false, "object"},
		"denominator a boolean":     {`{"v":{"numerator":1,"denominator":true}}`, false, false, "object"},
		"numerator not a number":    {`{"v":{"numerator":"1","denominator":2}}`, false, false, "object"},
		"rational of a bare object": {`{"v":{}}`, false, false, "object"},
	}
	for name, tc := range cases {
		t.Run(name, func(t *testing.T) {
			m, err := parseResponse(tc.raw)
			if err != nil {
				t.Fatalf("parseResponse: %v", err)
			}
			_, ratErr := readRational(m["v"], "v")
			if (ratErr == nil) != tc.asRational {
				t.Errorf("as a rational: error %v, want accepted = %v", ratErr, tc.asRational)
			}
			if want := "reply v: expected a rational, got " + tc.arrival; ratErr != nil && ratErr.Error() != want {
				t.Errorf("as a rational: got %q, want %q", ratErr, want)
			}
			_, intErr := readInt64(m["v"], "v")
			if (intErr == nil) != tc.asInteger {
				t.Errorf("as an integer: error %v, want accepted = %v", intErr, tc.asInteger)
			}
			if want := "reply v: expected number, got " + tc.arrival; intErr != nil && intErr.Error() != want {
				t.Errorf("as an integer: got %q, want %q", intErr, want)
			}
		})
	}
}

// A negative denominator, which the kernel never writes, flips the sign as
// the other bindings' readers do, and a zero denominator is read as written.
func TestReadRational_ReadsTheDenominatorAsWritten(t *testing.T) {
	cases := map[string]Rational{
		`{"v":{"numerator":-4,"denominator":-2}}`: {Numerator: Uint128{Lo: 4}, Denominator: Uint128{Lo: 2}},
		`{"v":{"numerator":4,"denominator":-2}}`:  {Negative: true, Numerator: Uint128{Lo: 4}, Denominator: Uint128{Lo: 2}},
		`{"v":{"numerator":1,"denominator":0}}`:   {Numerator: Uint128{Lo: 1}},
	}
	for raw, want := range cases {
		m, err := parseResponse(raw)
		if err != nil {
			t.Fatalf("parseResponse: %v", err)
		}
		got, err := readRational(m["v"], "v")
		if err != nil || got != want {
			t.Errorf("%s: got %+v, %v; want %+v", raw, got, err, want)
		}
	}
}
