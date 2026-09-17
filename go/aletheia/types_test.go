// SPDX-FileCopyrightText: 2025 Nicolas Pelletier
// SPDX-License-Identifier: BSD-2-Clause

package aletheia_test

import (
	"errors"
	"testing"
	"time"

	"github.com/aletheia-automotive/aletheia-go/v5/aletheia"
)

// The validated types: what each constructor takes, what it refuses, and how
// each value reads.

// lengthCodes is every frame length code and the payload it stands for,
// written here rather than read from the package so that the package's own
// table is checked against something.
var lengthCodes = map[uint8]int{
	0: 0, 1: 1, 2: 2, 3: 3, 4: 4, 5: 5, 6: 6, 7: 7, 8: 8,
	9: 12, 10: 16, 11: 20, 12: 24, 13: 32, 14: 48, 15: 64,
}

// Each constructor takes the largest value of its range and refuses the next
// one, and every refusal is a validation error.
func TestConstructors_RangeAndRefusal(t *testing.T) {
	cases := map[string]struct {
		accept func() error
		refuse func() error
	}{
		"standard identifier": {
			func() error { _, err := aletheia.NewStandardID(2047); return err },
			func() error { _, err := aletheia.NewStandardID(2048); return err },
		},
		"extended identifier": {
			func() error { _, err := aletheia.NewExtendedID(536870911); return err },
			func() error { _, err := aletheia.NewExtendedID(536870912); return err },
		},
		"length code": {
			func() error { _, err := aletheia.NewDLC(15); return err },
			func() error { _, err := aletheia.NewDLC(16); return err },
		},
		"bit position": {
			func() error { _, err := aletheia.NewBitPosition(aletheia.MaxBitPosition); return err },
			func() error { _, err := aletheia.NewBitPosition(aletheia.MaxBitPosition + 1); return err },
		},
		"bit length": {
			func() error { _, err := aletheia.NewBitLength(aletheia.MaxBitLength); return err },
			func() error { _, err := aletheia.NewBitLength(aletheia.MaxBitLength + 1); return err },
		},
		"a length of no bits": {
			func() error { _, err := aletheia.NewBitLength(1); return err },
			func() error { _, err := aletheia.NewBitLength(0); return err },
		},
		"payload length": {
			func() error { _, err := aletheia.BytesToDLC(64); return err },
			func() error { _, err := aletheia.BytesToDLC(65); return err },
		},
	}
	for name, tc := range cases {
		t.Run(name, func(t *testing.T) {
			if err := tc.accept(); err != nil {
				t.Errorf("the largest value of the range was refused: %v", err)
			}
			err := tc.refuse()
			if err == nil {
				t.Fatal("a value past the range was accepted")
			}
			var aErr *aletheia.Error
			if !errors.As(err, &aErr) {
				t.Fatalf("the refusal is %T, want the binding's error", err)
			}
			if aErr.Kind != aletheia.ErrValidation {
				t.Errorf("the refusal is %s, want a validation error", aErr.Kind)
			}
		})
	}
}

// An identifier carries its number and says which kind it is.
func TestIdentifiers_CarryTheirValue(t *testing.T) {
	sid, err := aletheia.NewStandardID(2047)
	if err != nil {
		t.Fatalf("NewStandardID: %v", err)
	}
	if sid.Value() != 2047 || sid.IsExtended() {
		t.Errorf("standard identifier = %d, extended = %v", sid.Value(), sid.IsExtended())
	}
	eid, err := aletheia.NewExtendedID(536870911)
	if err != nil {
		t.Fatalf("NewExtendedID: %v", err)
	}
	if eid.Value() != 536870911 || !eid.IsExtended() {
		t.Errorf("extended identifier = %d, extended = %v", eid.Value(), eid.IsExtended())
	}
}

// Every length code stands for its payload, and every payload maps back to
// that code, so the two directions of the package's table agree with this one.
func TestLengthCodes_BothDirections(t *testing.T) {
	for code, length := range lengthCodes {
		d, err := aletheia.NewDLC(code)
		if err != nil {
			t.Fatalf("NewDLC(%d): %v", code, err)
		}
		if got := d.ToBytes(); got != length {
			t.Errorf("code %d stands for %d bytes, want %d", code, got, length)
		}
		back, err := aletheia.BytesToDLC(length)
		if err != nil {
			t.Fatalf("BytesToDLC(%d): %v", length, err)
		}
		if back.Value() != code {
			t.Errorf("%d bytes maps to code %d, want %d", length, back.Value(), code)
		}
	}
	for _, length := range []int{9, 10, 11, 13, 15, 33, 65, -1, 100} {
		if _, err := aletheia.BytesToDLC(length); err == nil {
			t.Errorf("%d bytes was taken as a payload length", length)
		}
	}
}

// A time in microseconds reads as the duration it is.
func TestTimes_ReadAsDurations(t *testing.T) {
	if got := (aletheia.Timestamp{Microseconds: 1_000_000}).Duration(); got != time.Second {
		t.Errorf("a million microseconds read as %v", got)
	}
	if got := (aletheia.TimeBound{Microseconds: 5_000_000}).Duration(); got != 5*time.Second {
		t.Errorf("five million microseconds read as %v", got)
	}
	if got := (aletheia.TimeBound{Microseconds: 0}).Duration(); got != 0 {
		t.Errorf("no microseconds read as %v", got)
	}
}

// The three printed vocabularies read as the wire spells them.
func TestPrintedNames(t *testing.T) {
	cases := map[string]struct{ got, want string }{
		"holds":         {aletheia.Holds.String(), "holds"},
		"fails":         {aletheia.Fails.String(), "fails"},
		"unresolved":    {aletheia.Unresolved.String(), "unresolved"},
		"little endian": {aletheia.LittleEndian.String(), "little_endian"},
		"big endian":    {aletheia.BigEndian.String(), "big_endian"},
		"error":         {aletheia.SeverityError.String(), "error"},
		"warning":       {aletheia.SeverityWarning.String(), "warning"},
	}
	for name, tc := range cases {
		t.Run(name, func(t *testing.T) {
			if tc.got != tc.want {
				t.Errorf("printed as %q, want %q", tc.got, tc.want)
			}
		})
	}
}

// An identifier prints as hexadecimal, at the width its kind has.
func TestIdentifiers_Print(t *testing.T) {
	standard := map[uint16]string{0x123: "0x123", 0x001: "0x001", 0x000: "0x000", 0x7FF: "0x7FF"}
	for id, want := range standard {
		sid, err := aletheia.NewStandardID(id)
		if err != nil {
			t.Fatalf("NewStandardID(%d): %v", id, err)
		}
		if got := sid.String(); got != want {
			t.Errorf("standard %d printed as %q, want %q", id, got, want)
		}
	}
	extended := map[uint32]string{
		0x18FEF100: "0x18FEF100", 0x00000001: "0x00000001",
		0x00000000: "0x00000000", 0x1FFFFFFF: "0x1FFFFFFF",
	}
	for id, want := range extended {
		eid, err := aletheia.NewExtendedID(id)
		if err != nil {
			t.Fatalf("NewExtendedID(%d): %v", id, err)
		}
		if got := eid.String(); got != want {
			t.Errorf("extended %d printed as %q, want %q", id, got, want)
		}
	}
}

// An implication is the disjunction the logic has: the antecedent negated,
// beside the consequent.
func TestImpliesConstructor(t *testing.T) {
	a := aletheia.Atomic{Predicate: aletheia.LessThan{Signal: "Speed", Value: aletheia.IntRational(220)}}
	b := aletheia.Atomic{Predicate: aletheia.GreaterThan{Signal: "RPM", Value: aletheia.IntRational(500)}}

	or, ok := aletheia.Implies(a, b).(aletheia.Or)
	if !ok {
		t.Fatalf("an implication is %T, want a disjunction", aletheia.Implies(a, b))
	}
	notA, ok := or.Left.(aletheia.Not)
	if !ok {
		t.Fatalf("the left side is %T, want a negation", or.Left)
	}
	if _, ok := notA.Inner.(aletheia.Atomic); !ok {
		t.Fatalf("the negated side is %T, want the antecedent", notA.Inner)
	}
	if _, ok := or.Right.(aletheia.Atomic); !ok {
		t.Fatalf("the right side is %T, want the consequent", or.Right)
	}
}

// A rational reads as the number it is, for display; the exact value is the
// pair, which the wire carries.
func TestRational_Float64(t *testing.T) {
	cases := map[string]struct {
		r    aletheia.Rational
		want float64
	}{
		"three quarters": {aletheia.Rational{Numerator: 3, Denominator: 4}, 0.75},
		"one":            {aletheia.Rational{Numerator: 1, Denominator: 1}, 1.0},
		"nothing":        {aletheia.Rational{Numerator: 0, Denominator: 1}, 0.0},
		"a negative":     {aletheia.Rational{Numerator: -1, Denominator: 2}, -0.5},
		"seven thirds":   {aletheia.Rational{Numerator: 7, Denominator: 3}, 7.0 / 3.0},
	}
	for name, tc := range cases {
		t.Run(name, func(t *testing.T) {
			if got := tc.r.Float64(); got != tc.want {
				t.Errorf("read as %v, want %v", got, tc.want)
			}
		})
	}
}
