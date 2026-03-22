package aletheia

// Predicate is a signal predicate for LTL atomic propositions.
type Predicate interface {
	predicate() // sealed
}

// Equals tests whether a signal's value equals a specific value.
type Equals struct {
	Signal SignalName
	Value  PhysicalValue
}

// LessThan tests whether a signal's value is strictly less than a threshold.
type LessThan struct {
	Signal SignalName
	Value  PhysicalValue
}

// GreaterThan tests whether a signal's value is strictly greater than a threshold.
type GreaterThan struct {
	Signal SignalName
	Value  PhysicalValue
}

// LessThanOrEqual tests whether a signal's value is at most a threshold.
type LessThanOrEqual struct {
	Signal SignalName
	Value  PhysicalValue
}

// GreaterThanOrEqual tests whether a signal's value is at least a threshold.
type GreaterThanOrEqual struct {
	Signal SignalName
	Value  PhysicalValue
}

// Between tests whether a signal's value is within [Min, Max].
type Between struct {
	Signal SignalName
	Min    PhysicalValue
	Max    PhysicalValue
}

// ChangedBy tests whether a signal's value changed by at least Delta since the previous frame.
type ChangedBy struct {
	Signal SignalName
	Delta  Delta
}

func (Equals) predicate()             {}
func (LessThan) predicate()           {}
func (GreaterThan) predicate()        {}
func (LessThanOrEqual) predicate()    {}
func (GreaterThanOrEqual) predicate() {}
func (Between) predicate()            {}
func (ChangedBy) predicate()          {}

// Formula is an LTL formula over signal predicates.
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
	Bound Timestamp
	Inner Formula
}

// MetricEventually holds if the inner formula holds at some step within Bound.
type MetricEventually struct {
	Bound Timestamp
	Inner Formula
}

// MetricUntil is a time-bounded Until: Left holds until Right within Bound.
type MetricUntil struct {
	Bound Timestamp
	Left  Formula
	Right Formula
}

// MetricRelease is a time-bounded Release: Right holds until Left within Bound.
type MetricRelease struct {
	Bound Timestamp
	Left  Formula
	Right Formula
}

func (Atomic) formula()           {}
func (Not) formula()              {}
func (And) formula()              {}
func (Or) formula()               {}
func (Next) formula()             {}
func (Always) formula()           {}
func (Eventually) formula()       {}
func (Until) formula()            {}
func (Release) formula()          {}
func (MetricAlways) formula()     {}
func (MetricEventually) formula() {}
func (MetricUntil) formula()      {}
func (MetricRelease) formula()    {}

// Convenience constructors for common patterns.

// Never returns Always(Not(Atomic(p))).
func Never(p Predicate) Formula {
	return Always{Inner: Not{Inner: Atomic{Predicate: p}}}
}

// AlwaysWithin returns MetricAlways with the given bound.
func AlwaysWithin(bound Timestamp, f Formula) Formula {
	return MetricAlways{Bound: bound, Inner: f}
}

// EventuallyWithin returns MetricEventually with the given bound.
func EventuallyWithin(bound Timestamp, f Formula) Formula {
	return MetricEventually{Bound: bound, Inner: f}
}
