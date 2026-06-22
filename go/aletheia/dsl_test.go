// SPDX-FileCopyrightText: 2025 Nicolas Pelletier
// SPDX-License-Identifier: BSD-2-Clause

package aletheia_test

import (
	"testing"

	"github.com/aletheia-automotive/aletheia-go/aletheia"
)

// The fluent Signal(...) builder must produce exactly the same predicate
// structs as the bare struct literals — it is sugar, not a new wire shape.
// Predicate structs are comparable (SignalName + Rational fields), so we can
// assert struct equality directly.

func TestSignalBuilder_Equals(t *testing.T) {
	got := aletheia.Signal("Speed").Equals(aletheia.IntRational(220))
	want := aletheia.Equals{Signal: "Speed", Value: aletheia.IntRational(220)}
	if got != want {
		t.Errorf("got %#v, want %#v", got, want)
	}
}

func TestSignalBuilder_LessThan(t *testing.T) {
	got := aletheia.Signal("Speed").LessThan(aletheia.IntRational(220))
	want := aletheia.LessThan{Signal: "Speed", Value: aletheia.IntRational(220)}
	if got != want {
		t.Errorf("got %#v, want %#v", got, want)
	}
}

func TestSignalBuilder_GreaterThan(t *testing.T) {
	got := aletheia.Signal("Speed").GreaterThan(aletheia.IntRational(220))
	want := aletheia.GreaterThan{Signal: "Speed", Value: aletheia.IntRational(220)}
	if got != want {
		t.Errorf("got %#v, want %#v", got, want)
	}
}

func TestSignalBuilder_LessThanOrEqual(t *testing.T) {
	got := aletheia.Signal("Speed").LessThanOrEqual(aletheia.IntRational(220))
	want := aletheia.LessThanOrEqual{Signal: "Speed", Value: aletheia.IntRational(220)}
	if got != want {
		t.Errorf("got %#v, want %#v", got, want)
	}
}

func TestSignalBuilder_GreaterThanOrEqual(t *testing.T) {
	got := aletheia.Signal("Speed").GreaterThanOrEqual(aletheia.IntRational(220))
	want := aletheia.GreaterThanOrEqual{Signal: "Speed", Value: aletheia.IntRational(220)}
	if got != want {
		t.Errorf("got %#v, want %#v", got, want)
	}
}

// TestSignalBuilder_AllComparisons sweeps every builder method against its
// bare-struct equivalent in one table to guard against a method being wired to
// the wrong predicate constructor.
func TestSignalBuilder_AllComparisons(t *testing.T) {
	const sig = "Voltage"
	v := aletheia.IntRational(12)
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
	}
	for _, c := range cases {
		t.Run(c.name, func(t *testing.T) {
			if c.got != c.want {
				t.Errorf("got %#v, want %#v", c.got, c.want)
			}
		})
	}
}

// TestSignalBuilder_ComposesIntoFormula confirms the builder's Predicate drops
// straight into the formula combinators and renders identically to the bare
// struct via FormatFormula — i.e. it is wire/format-symmetric, not a parallel path.
func TestSignalBuilder_ComposesIntoFormula(t *testing.T) {
	pred := aletheia.Signal("Speed").LessThanOrEqual(aletheia.IntRational(220))
	fluent := aletheia.Always{Inner: aletheia.Atomic{Predicate: pred}}

	bare := aletheia.Always{Inner: aletheia.Atomic{Predicate: aletheia.LessThanOrEqual{
		Signal: "Speed",
		Value:  aletheia.IntRational(220),
	}}}

	gotFluent := aletheia.FormatFormula(fluent)
	gotBare := aletheia.FormatFormula(bare)
	if gotFluent != gotBare {
		t.Errorf("fluent formatted %q, bare formatted %q; must match", gotFluent, gotBare)
	}

	const want = "always(Speed <= 220)"
	if gotFluent != want {
		t.Errorf("FormatFormula = %q, want %q", gotFluent, want)
	}
}
