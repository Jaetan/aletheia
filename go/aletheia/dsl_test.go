//go:build cgo && linux

// SPDX-FileCopyrightText: 2025 Nicolas Pelletier
// SPDX-License-Identifier: BSD-2-Clause

package aletheia_test

import (
	"testing"

	"github.com/aletheia-automotive/aletheia-go/aletheia"
)

// The Signal builder is sugar: each method produces the same predicate struct
// as the bare literal, compared by value since the predicates are comparable.
func TestSignalBuilder_MatchesLiterals(t *testing.T) {
	const sig = "Voltage"
	v := aletheia.IntRational(12)
	hi := aletheia.IntRational(14)
	b := aletheia.Signal(sig)
	cases := []struct {
		name string
		got  aletheia.Predicate
		want aletheia.Predicate
	}{
		{"Equals", b.Equals(v), aletheia.Equals{Signal: sig, Value: v}},
		{"LessThan", b.LessThan(v), aletheia.LessThan{Signal: sig, Value: v}},
		{"GreaterThan", b.GreaterThan(v), aletheia.GreaterThan{Signal: sig, Value: v}},
		{"LessThanOrEqual", b.LessThanOrEqual(v), aletheia.LessThanOrEqual{Signal: sig, Value: v}},
		{"GreaterThanOrEqual", b.GreaterThanOrEqual(v), aletheia.GreaterThanOrEqual{Signal: sig, Value: v}},
		{"Between", b.Between(v, hi), aletheia.Between{Signal: sig, Min: v, Max: hi}},
		{"ChangedBy", b.ChangedBy(v), aletheia.ChangedBy{Signal: sig, Delta: v}},
		{"StableWithin", b.StableWithin(v), aletheia.StableWithin{Signal: sig, Tolerance: v}},
	}
	for _, c := range cases {
		t.Run(c.name, func(t *testing.T) {
			if c.got != c.want {
				t.Errorf("got %#v, want %#v", c.got, c.want)
			}
		})
	}
}

// A built predicate drops into the formula combinators and prints as the
// bare struct does.
func TestSignalBuilder_ComposesIntoFormula(t *testing.T) {
	fluent := aletheia.Always{Inner: aletheia.Atomic{Predicate: aletheia.Signal("Speed").LessThanOrEqual(aletheia.IntRational(220))}}
	bare := aletheia.Always{Inner: aletheia.Atomic{Predicate: aletheia.LessThanOrEqual{Signal: "Speed", Value: aletheia.IntRational(220)}}}
	gotFluent, gotBare := aletheia.FormatFormula(fluent), aletheia.FormatFormula(bare)
	if gotFluent != gotBare {
		t.Errorf("fluent formatted %q, bare formatted %q", gotFluent, gotBare)
	}
	const want = "always(Speed <= 220)"
	if gotFluent != want {
		t.Errorf("FormatFormula = %q, want %q", gotFluent, want)
	}
}
