//go:build cgo && linux

// SPDX-FileCopyrightText: 2025 Nicolas Pelletier
// SPDX-License-Identifier: BSD-2-Clause

package aletheia

import (
	"errors"
	"testing"
)

// FromDecimal is the cross-binding decimal SSOT: it delegates to the verified
// Agda kernel (aletheia_parse_decimal) and decodes via the shared wire decoder.
// These parity cases mirror python/tests/test_parse_decimal_ffi.py and the Rust
// decimal_ssot test, and (with the success/overflow halves) carry the coverage
// the retired float-rejecting check-builder test used to provide: a malformed or
// overflowing user value FAILS rather than silently clamping. RTS-gated, so it
// needs the runtime TestMain (main_test.go) brings up package-wide.

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
		{"-0", 0, 1},    // negative zero collapses to +0
		{"0.000", 0, 1}, // trailing-zero fraction canonicalises
		{"0.10", 1, 10}, // trailing zero trimmed
		{"00.1", 1, 10}, // leading zeros accepted
		{"9223372036854775807", 9223372036854775807, 1}, // Int64 max fits
	}
	for _, c := range cases {
		r, err := FromDecimal(c.in)
		if err != nil {
			t.Errorf("FromDecimal(%q): unexpected error: %v", c.in, err)
			continue
		}
		if r.Numerator != c.num || r.Denominator != c.den {
			t.Errorf("FromDecimal(%q) = %d/%d, want %d/%d", c.in, r.Numerator, r.Denominator, c.num, c.den)
		}
	}
}

func TestFromDecimalRejectsMalformed(t *testing.T) {
	// Malformed per the grammar -?digits[.digits+]: no '+', no leading '.', no
	// exponent, no fraction syntax, and full consumption (trailing input rejected).
	for _, in := range []string{"3.14xyz", "1e3", ".5", "+1", "1/2", "1.", "1 ", " 1", "", "-"} {
		_, err := FromDecimal(in)
		if err == nil {
			t.Errorf("FromDecimal(%q): expected parse error, got nil", in)
			continue
		}
		var aErr *Error
		if !errors.As(err, &aErr) || aErr.Kind != ErrValidation {
			t.Errorf("FromDecimal(%q): expected ErrValidation, got %v", in, err)
		}
	}
}

func TestFromDecimalRejectsOverflow(t *testing.T) {
	// A numerator or denominator beyond the Int64 wire range is rejected as a
	// validation error (user input), not silently clamped.
	for _, in := range []string{"99999999999999999999.5", "0.0000000000000000001"} {
		_, err := FromDecimal(in)
		if err == nil {
			t.Errorf("FromDecimal(%q): expected overflow error, got nil", in)
			continue
		}
		var aErr *Error
		if !errors.As(err, &aErr) || aErr.Kind != ErrValidation {
			t.Errorf("FromDecimal(%q): expected ErrValidation, got %v", in, err)
		}
	}
}
