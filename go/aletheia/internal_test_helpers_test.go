// SPDX-FileCopyrightText: 2025 Nicolas Pelletier
// SPDX-License-Identifier: BSD-2-Clause

package aletheia

import (
	"errors"
	"math"
	"strings"
	"testing"
)

// The helpers the tests inside the package share; helpers_test.go carries the
// same claims for the tests outside, which cannot reach an unexported name.

// requireErrorContains holds that the failure is the package's error type,
// through whatever wraps it, and that its message carries the substring.
func requireErrorContains(t *testing.T, err error, substr string) {
	t.Helper()
	if err == nil {
		t.Fatal("expected error, got nil")
	}
	var e *Error
	if !errors.As(err, &e) {
		t.Fatalf("expected *Error, got %T: %v", err, err)
	}
	if !strings.Contains(err.Error(), substr) {
		t.Errorf("expected error containing %q, got: %v", substr, err)
	}
}

// requireRefused holds that the failure is a validation [*Error] carrying the
// kernel's code and printing exactly the text given.
func requireRefused(t *testing.T, err error, code ErrorCode, text string) {
	t.Helper()
	var e *Error
	if !errors.As(err, &e) {
		t.Fatalf("expected *Error, got %T: %v", err, err)
	}
	if e.Kind != ErrValidation || e.Code != code {
		t.Errorf("kind %v, code %q; want %v, %q", e.Kind, e.Code, ErrValidation, code)
	}
	if got := err.Error(); got != text {
		t.Errorf("got %q, want %q", got, text)
	}
}

// requireReplyRefusal holds that the failure is a reply reader's refusal: a
// protocol [*Error] with no code, printing exactly the text given.
func requireReplyRefusal(t *testing.T, err error, text string) {
	t.Helper()
	var e *Error
	if !errors.As(err, &e) {
		t.Fatalf("expected *Error, got %T: %v", err, err)
	}
	if e.Kind != ErrProtocol || e.Code != "" {
		t.Errorf("kind %v, code %q; want %v with no code", e.Kind, e.Code, ErrProtocol)
	}
	if got := err.Error(); got != text {
		t.Errorf("got %q, want %q", got, text)
	}
}

// rationalBound is MaxRationalComponentMagnitude, 2^128-1, as a bound
// refusal carries it.
var rationalBound = Uint128{Hi: math.MaxUint64, Lo: math.MaxUint64}

// ratOf is the exact rational n over d, carrying the quotient's sign, for the
// small values the tests write; a wider one is written as a Rational literal.
func ratOf(n, d int64) Rational {
	num, den := IntRational(n), IntRational(d)
	return Rational{Negative: num.Negative != den.Negative && n != 0, Numerator: num.Numerator, Denominator: den.Numerator}
}

// must is v once err is nil, for a builder the test holds the kernel accepts;
// any refusal panics, failing the test that built it.
func must[V any](v V, err error) V {
	if err != nil {
		panic(err)
	}
	return v
}
