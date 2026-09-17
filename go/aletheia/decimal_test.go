//go:build cgo && linux

// SPDX-FileCopyrightText: 2025 Nicolas Pelletier
// SPDX-License-Identifier: BSD-2-Clause

// FromDecimal delegates to the kernel's decimal parser and decodes through the
// shared wire decoder; these cases are the ones python/tests/
// test_parse_decimal_ffi.py and rust/tests/decimal_ssot.rs run, so the
// bindings agree on what parses and what is refused. The runtime the calls
// need is the one TestMain brings up.

package aletheia

import (
	"errors"
	"testing"
)

// Valid literals parse to the exact rational, canonicalised: a negative zero
// is zero, trailing fraction zeros are trimmed, leading zeros are accepted,
// and the largest int64 fits.
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

// Every refusal is a validation error, the kind for user input: a literal
// outside the grammar (an optional minus, digits, optionally a point and
// digits, consumed whole), a rational past int64, and a non-ASCII byte, whose
// echo in the error envelope must still be valid JSON for the refusal to
// arrive as a validation error rather than a protocol one.
func TestFromDecimalRefusals(t *testing.T) {
	groups := map[string][]string{
		"malformed": {"3.14xyz", "1e3", ".5", "+1", "1/2", "1.", "1 ", " 1", "", "-"},
		"overflow":  {"99999999999999999999.5", "0.0000000000000000001"},
		"non-ascii": {"1.5€"},
	}
	for group, inputs := range groups {
		for _, in := range inputs {
			_, err := FromDecimal(in)
			if err == nil {
				t.Errorf("%s: FromDecimal(%q) accepted", group, in)
				continue
			}
			var aErr *Error
			if !errors.As(err, &aErr) || aErr.Kind != ErrValidation {
				t.Errorf("%s: FromDecimal(%q): expected ErrValidation, got %v", group, in, err)
			}
		}
	}
}
