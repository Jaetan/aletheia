//go:build cgo && linux

// SPDX-FileCopyrightText: 2025 Nicolas Pelletier
// SPDX-License-Identifier: BSD-2-Clause

// FromDecimal delegates to the kernel's decimal parser and reads its refusal
// through the envelope reader the binary-output entries share; these cases are
// the ones python/tests/test_parse_decimal_ffi.py and rust/tests/decimal_ssot.rs
// run, so the bindings agree on what parses and what is refused. The runtime
// the calls need is the one TestMain brings up.

package aletheia

import (
	"errors"
	"fmt"
	"math"
	"strings"
	"testing"
)

// Valid literals parse to the exact rational, canonicalised: a negative zero
// is zero, trailing fraction zeros are trimmed, leading zeros are accepted,
// a magnitude past 64 bits is carried, and the magnitude bound 2^128-1 fits,
// as does its negation.
func TestFromDecimalSuccess(t *testing.T) {
	cases := []struct {
		in   string
		want Rational
	}{
		{"3.14", ratOf(157, 50)},
		{"42", ratOf(42, 1)},
		{"0.1", ratOf(1, 10)},
		{"-3.14", ratOf(-157, 50)},
		{"0", ratOf(0, 1)},
		{"-0", ratOf(0, 1)},
		{"0.000", ratOf(0, 1)},
		{"0.10", ratOf(1, 10)},
		{"00.1", ratOf(1, 10)},
		{"9223372036854775807", ratOf(math.MaxInt64, 1)},
		{"-9223372036854775808", ratOf(math.MinInt64, 1)},
		{"99999999999999999999.5", Rational{Numerator: Uint128{Hi: 10, Lo: 15532559262904483839}, Denominator: Uint128{Lo: 2}}},
		{"340282366920938463463374607431768211455", Rational{Numerator: rationalBound, Denominator: Uint128{Lo: 1}}},
		{"-340282366920938463463374607431768211455", Rational{Negative: true, Numerator: rationalBound, Denominator: Uint128{Lo: 1}}},
	}
	for _, c := range cases {
		r, err := FromDecimal(c.in)
		if err != nil {
			t.Errorf("FromDecimal(%q): unexpected error: %v", c.in, err)
			continue
		}
		if r != c.want {
			t.Errorf("FromDecimal(%q) = %+v, want %+v", c.in, r, c.want)
		}
	}
}

// A literal outside the grammar (an optional minus, digits, optionally a point
// and digits, consumed whole) is refused by the kernel's parser with the line
// and column it stopped at: text_parse_failure where nothing parsed,
// text_trailing_input where a number parsed and characters followed. A
// non-ASCII literal is a grammar failure, not an encoding one. An interior NUL
// and bytes that are not UTF-8 are the shim's own refusal; each surrounds
// digits that are a literal without them, so dropping them, or reading the
// literal only up to the NUL, would accept it.
func TestFromDecimalCodedRefusals(t *testing.T) {
	kernel := map[string]struct {
		code   ErrorCode
		column int
	}{
		"3.14xyz": {CodeTextTrailingInput, 5},
		"1e3":     {CodeTextTrailingInput, 2},
		".5":      {CodeTextParseFailure, 1},
		"+1":      {CodeTextParseFailure, 1},
		"1/2":     {CodeTextTrailingInput, 2},
		"1.":      {CodeTextTrailingInput, 3},
		"1 ":      {CodeTextTrailingInput, 2},
		" 1":      {CodeTextParseFailure, 1},
		"":        {CodeTextParseFailure, 1},
		"-":       {CodeTextParseFailure, 2},
		"1.5€":    {CodeTextTrailingInput, 4},
	}
	for in, want := range kernel {
		_, err := FromDecimal(in)
		var aErr *Error
		if !errors.As(err, &aErr) || aErr.Kind != ErrValidation || aErr.Code != want.code {
			t.Errorf("FromDecimal(%q): want a validation error with code %q, got %v", in, want.code, err)
			continue
		}
		at := fmt.Sprintf("parse failed at line 1, column %d", want.column)
		if !strings.Contains(aErr.Message, at) {
			t.Errorf("FromDecimal(%q): message %q does not say %q", in, aErr.Message, at)
		}
	}
	shim := map[string]string{
		"1\x00xyz":       "input contains a NUL byte",
		"1.5\xff":        "input is not valid UTF-8",
		"1\xe2\x82.5":    "input is not valid UTF-8",
		"1\xed\xa0\x805": "input is not valid UTF-8",
		"\xc0\x801":      "input is not valid UTF-8",
	}
	for in, message := range shim {
		_, err := FromDecimal(in)
		var aErr *Error
		if !errors.As(err, &aErr) || aErr.Kind != ErrValidation || aErr.Code != CodeFFIValidationError || aErr.Message != message {
			t.Errorf("FromDecimal(%q): want a validation error ffi_validation_error %q, got %v", in, message, err)
		}
	}
}

// A numerator or denominator whose magnitude is past the kernel's rational
// component bound, 2^128-1, is the typed bound refusal, its field "decimal":
// a forty-digit integer part, thirty-nine decimal places and one past the
// bound on the negative side. The kernel reports a magnitude up to the bound,
// so each observes the bound and the message names no number.
func TestFromDecimalBoundRefusals(t *testing.T) {
	message := "decimal: rational component magnitude exceeds limit 340282366920938463463374607431768211455"
	for _, in := range []string{
		"1" + strings.Repeat("0", 39),
		"0." + strings.Repeat("0", 38) + "1",
		"-340282366920938463463374607431768211456",
	} {
		_, err := FromDecimal(in)
		var bex *InputBoundExceededError
		if !errors.As(err, &bex) {
			t.Errorf("FromDecimal(%q): want *InputBoundExceededError, got %v", in, err)
			continue
		}
		if bex.Code != CodeInputBoundExceeded || bex.BoundKind != BoundKindRationalComponentMagnitude ||
			bex.Field != "decimal" || bex.Observed != rationalBound || bex.Limit != rationalBound {
			t.Errorf("FromDecimal(%q): code %q kind %q field %q observed %s limit %s, want %q %q %q %s %s",
				in, bex.Code, bex.BoundKind, bex.Field, bex.Observed, bex.Limit,
				CodeInputBoundExceeded, BoundKindRationalComponentMagnitude, "decimal", rationalBound, rationalBound)
		}
		if got := bex.Error(); got != message {
			t.Errorf("FromDecimal(%q): Error() = %q, want %q", in, got, message)
		}
	}
}
