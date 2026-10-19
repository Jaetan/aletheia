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
	"strings"
	"testing"
)

// Valid literals parse to the exact rational, canonicalised: a negative zero
// is zero, trailing fraction zeros are trimmed, leading zeros are accepted,
// and the largest int64 fits, as does its negation.
func TestFromDecimalSuccess(t *testing.T) {
	cases := []struct {
		in       string
		num, den int64
	}{
		{"3.14", 157, 50},
		{"42", 42, 1},
		{"0.1", 1, 10},
		{"-3.14", -157, 50},
		{"0", 0, 1},
		{"-0", 0, 1},
		{"0.000", 0, 1},
		{"0.10", 1, 10},
		{"00.1", 1, 10},
		{"9223372036854775807", 9223372036854775807, 1},
		{"-9223372036854775807", -9223372036854775807, 1},
	}
	for _, c := range cases {
		r, err := FromDecimal(c.in)
		if err != nil {
			t.Errorf("FromDecimal(%q): unexpected error: %v", c.in, err)
			continue
		}
		if r != (Rational{Numerator: c.num, Denominator: c.den}) {
			t.Errorf("FromDecimal(%q) = %d/%d, want %d/%d", c.in, r.Numerator, r.Denominator, c.num, c.den)
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
		code   string
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
// component bound is the typed bound refusal, its field "decimal": the most
// negative int64 is one past the bound and a fraction of nineteen decimal
// places has a denominator past it, each observed exact; a numerator of
// twenty-one digits is past what the kernel measures, observed saturated.
func TestFromDecimalBoundRefusals(t *testing.T) {
	observed := map[string]uint64{
		"99999999999999999999.5": 18446744073709551615,
		"0.0000000000000000001":  10000000000000000000,
		"-9223372036854775808":   9223372036854775808,
	}
	for in, want := range observed {
		_, err := FromDecimal(in)
		var bex *InputBoundExceededError
		if !errors.As(err, &bex) {
			t.Errorf("FromDecimal(%q): want *InputBoundExceededError, got %v", in, err)
			continue
		}
		if bex.Code != CodeInputBoundExceeded || bex.Field != "decimal" || bex.Observed != want || bex.Limit != 9223372036854775807 {
			t.Errorf("FromDecimal(%q): code %q field %q observed %d limit %d, want %q %q %d %d",
				in, bex.Code, bex.Field, bex.Observed, bex.Limit, CodeInputBoundExceeded, "decimal", want, uint64(9223372036854775807))
		}
	}
}

// A rational over a non-positive denominator is refused as the malfunction it
// would be, since the kernel answers every denominator positive.
func TestDecimalAnswersTheKernelNeverGives(t *testing.T) {
	var aErr *Error
	for _, den := range []int64{0, -1} {
		_, err := decimalValue(1, den)
		if !errors.As(err, &aErr) || aErr.Kind != ErrProtocol {
			t.Errorf("decimalValue(1, %d): %v", den, err)
		}
	}
	if r, err := decimalValue(1, 2); err != nil || r != (Rational{Numerator: 1, Denominator: 2}) {
		t.Errorf("decimalValue(1, 2) = %v, %v", r, err)
	}
}
