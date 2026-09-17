// SPDX-FileCopyrightText: 2025 Nicolas Pelletier
// SPDX-License-Identifier: BSD-2-Clause

package aletheia

// Predicate is a test on one signal's value, the leaf of a formula. Only the
// types below implement it: the method it requires is unexported, so a value
// of this interface is always one the kernel knows.
//
// Every value a predicate carries is an exact [Rational], never a float, which
// is what lets the kernel decide the comparison rather than approximate it.
// Build one with [IntRational] for a whole number, or with [FromDecimal] for
// decimal text, which the kernel parses.
type Predicate interface {
	predicate() // sealed
}

// Equals tests whether a signal's value equals a specific value.
type Equals struct {
	Signal SignalName
	Value  Rational
}

// LessThan tests whether a signal's value is strictly less than a threshold.
type LessThan struct {
	Signal SignalName
	Value  Rational
}

// GreaterThan tests whether a signal's value is strictly greater than a threshold.
type GreaterThan struct {
	Signal SignalName
	Value  Rational
}

// LessThanOrEqual tests whether a signal's value is at most a threshold.
type LessThanOrEqual struct {
	Signal SignalName
	Value  Rational
}

// GreaterThanOrEqual tests whether a signal's value is at least a threshold.
type GreaterThanOrEqual struct {
	Signal SignalName
	Value  Rational
}

// Between tests whether a signal's value is within [Min, Max].
type Between struct {
	Signal SignalName
	Min    Rational
	Max    Rational
}

// ChangedBy tests how far a signal moved since the previous frame. A positive
// delta asks for a rise of at least that much, a negative one for a fall.
type ChangedBy struct {
	Signal SignalName
	Delta  Rational
}

// StableWithin tests whether a signal's value stayed within Tolerance of its previous value.
type StableWithin struct {
	Signal    SignalName
	Tolerance Rational
}

func (Equals) predicate()             {}
func (LessThan) predicate()           {}
func (GreaterThan) predicate()        {}
func (LessThanOrEqual) predicate()    {}
func (GreaterThanOrEqual) predicate() {}
func (Between) predicate()            {}
func (ChangedBy) predicate()          {}
func (StableWithin) predicate()       {}

// SignalBuilder names a signal and builds every predicate the kernel has over
// it: the five comparisons, the range, and the two that read the previous
// frame as well as this one.
//
// This is the formula-level builder. [CheckSignal] is the other one, which
// names and builds whole checks.
type SignalBuilder struct {
	name SignalName
}

// Signal names the signal a predicate is about:
//
//	aletheia.Signal("Speed").LessThanOrEqual(aletheia.IntRational(220))
//
// The predicate it returns goes inside [Atomic], or straight into [Always],
// [Eventually] and the rest through it.
func Signal(name string) SignalBuilder { return SignalBuilder{name: SignalName(name)} }

// None of these can fail. A threshold is already an exact rational, and the
// two that can be asked for something impossible, a range whose minimum is
// above its maximum and a negative tolerance, are refused where the property
// is serialised, which is the one place every route to a predicate passes
// through: a caller may also write the value directly.

// Equals holds when the signal's value is exactly v.
func (s SignalBuilder) Equals(v Rational) Predicate { return Equals{Signal: s.name, Value: v} }

// LessThan holds when the value is below v.
func (s SignalBuilder) LessThan(v Rational) Predicate { return LessThan{Signal: s.name, Value: v} }

// GreaterThan holds when the value is above v.
func (s SignalBuilder) GreaterThan(v Rational) Predicate {
	return GreaterThan{Signal: s.name, Value: v}
}

// LessThanOrEqual holds when the value is at most v.
func (s SignalBuilder) LessThanOrEqual(v Rational) Predicate {
	return LessThanOrEqual{Signal: s.name, Value: v}
}

// GreaterThanOrEqual holds when the value is at least v.
func (s SignalBuilder) GreaterThanOrEqual(v Rational) Predicate {
	return GreaterThanOrEqual{Signal: s.name, Value: v}
}

// Between holds when the value is at least lo and at most hi.
func (s SignalBuilder) Between(lo, hi Rational) Predicate {
	return Between{Signal: s.name, Min: lo, Max: hi}
}

// ChangedBy holds when the signal moved by at least delta since the previous
// frame, a positive delta asking for a rise and a negative one for a fall.
func (s SignalBuilder) ChangedBy(delta Rational) Predicate {
	return ChangedBy{Signal: s.name, Delta: delta}
}

// StableWithin holds when the signal stayed within tolerance of its value in
// the previous frame.
func (s SignalBuilder) StableWithin(tolerance Rational) Predicate {
	return StableWithin{Signal: s.name, Tolerance: tolerance}
}

// Formula is a property over a trace of frames, built from predicates. Only
// the types below implement it, the method it requires being unexported.
type Formula interface {
	formula() // sealed
}

// Atomic wraps a Predicate as a formula leaf.
type Atomic struct{ Predicate Predicate }

// Not is the logical negation of a formula.
type Not struct{ Inner Formula }

// And is the logical conjunction of two formulas.
type And struct{ Left, Right Formula }

// Or is the logical disjunction of two formulas.
type Or struct{ Left, Right Formula }

// Next holds if the inner formula holds at the next time step.
type Next struct{ Inner Formula }

// WeakNext holds if the inner formula holds at the next time step, or
// vacuously at the end of the trace (no successor frame).
type WeakNext struct{ Inner Formula }

// Always holds if the inner formula holds at every future time step.
type Always struct{ Inner Formula }

// Eventually holds if the inner formula holds at some future time step.
type Eventually struct{ Inner Formula }

// Until holds if Left holds until Right becomes true.
type Until struct{ Left, Right Formula }

// Release holds if Right holds until (and including when) Left becomes true.
type Release struct{ Left, Right Formula }

// MetricAlways holds if the inner formula holds for every step within Bound.
type MetricAlways struct {
	Bound TimeBound
	Inner Formula
}

// MetricEventually holds if the inner formula holds at some step within Bound.
type MetricEventually struct {
	Bound TimeBound
	Inner Formula
}

// MetricUntil is a time-bounded Until: Left holds until Right within Bound.
type MetricUntil struct {
	Bound TimeBound
	Left  Formula
	Right Formula
}

// MetricRelease is a time-bounded Release: Right holds until Left within Bound.
type MetricRelease struct {
	Bound TimeBound
	Left  Formula
	Right Formula
}

func (Atomic) formula()           {}
func (Not) formula()              {}
func (And) formula()              {}
func (Or) formula()               {}
func (Next) formula()             {}
func (WeakNext) formula()         {}
func (Always) formula()           {}
func (Eventually) formula()       {}
func (Until) formula()            {}
func (Release) formula()          {}
func (MetricAlways) formula()     {}
func (MetricEventually) formula() {}
func (MetricUntil) formula()      {}
func (MetricRelease) formula()    {}

// The shapes common enough to have a name of their own.

// Never holds when the predicate holds at no frame.
func Never(p Predicate) Formula {
	return Always{Inner: Not{Inner: Atomic{Predicate: p}}}
}

// AlwaysWithin holds when the formula holds at every frame inside the bound.
func AlwaysWithin(bound TimeBound, f Formula) Formula {
	return MetricAlways{Bound: bound, Inner: f}
}

// EventuallyWithin holds when the formula holds at some frame inside the bound.
func EventuallyWithin(bound TimeBound, f Formula) Formula {
	return MetricEventually{Bound: bound, Inner: f}
}

// Implies holds when the consequent holds at every frame the antecedent does,
// which is the disjunction the logic has rather than a connective of its own.
func Implies(antecedent, consequent Formula) Formula {
	return Or{Left: Not{Inner: antecedent}, Right: consequent}
}
