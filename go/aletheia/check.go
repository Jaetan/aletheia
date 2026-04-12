package aletheia

import (
	"fmt"
	"math"
)

// CheckResult is the terminal object produced by a check builder chain.
// It wraps an LTL formula with optional metadata for display/reporting.
// Metadata (name, severity) is not sent to the Agda core.
type CheckResult struct {
	formula       Formula
	name          string
	severity      string
	signalName    string
	conditionDesc string
}

// Formula returns the LTL formula for this check.
func (r CheckResult) Formula() Formula { return r.formula }

// Named returns a copy with the given human-readable name.
func (r CheckResult) Named(name string) CheckResult {
	r.name = name
	return r
}

// Severity returns a copy with the given severity level.
func (r CheckResult) Severity(level string) CheckResult {
	r.severity = level
	return r
}

// Name returns the check name.
func (r CheckResult) Name() string { return r.name }

// CheckSeverity returns the check severity.
func (r CheckResult) CheckSeverity() string { return r.severity }

// SignalName returns the primary signal name for this check.
func (r CheckResult) SignalName() SignalName { return SignalName(r.signalName) }

// ConditionDesc returns a human-readable description of the check condition.
func (r CheckResult) ConditionDesc() string { return r.conditionDesc }

// ---------------------------------------------------------------------------
// Single-signal check builders
// ---------------------------------------------------------------------------

// CheckSignalBuilder builds single-signal checks.
type CheckSignalBuilder struct {
	name string
}

// CheckSignal begins a single-signal check.
func CheckSignal(name string) CheckSignalBuilder {
	return CheckSignalBuilder{name: name}
}

// NeverExceeds produces G(signal < value).
func (b CheckSignalBuilder) NeverExceeds(value PhysicalValue) CheckResult {
	f := Always{Inner: Atomic{Predicate: LessThan{Signal: SignalName(b.name), Value: value}}}
	return CheckResult{
		formula: f, signalName: b.name,
		conditionDesc: fmt.Sprintf("< %g", float64(value)),
	}
}

// NeverBelow produces G(signal >= value).
func (b CheckSignalBuilder) NeverBelow(value PhysicalValue) CheckResult {
	f := Always{Inner: Atomic{Predicate: GreaterThanOrEqual{Signal: SignalName(b.name), Value: value}}}
	return CheckResult{
		formula: f, signalName: b.name,
		conditionDesc: fmt.Sprintf(">= %g", float64(value)),
	}
}

// StaysBetween produces G(lo <= signal <= hi).
// Returns an error if lo > hi (inverted range is always false).
func (b CheckSignalBuilder) StaysBetween(lo, hi PhysicalValue) (CheckResult, error) {
	if lo > hi {
		return CheckResult{}, validationError(fmt.Sprintf("stays_between: lo (%g) must be <= hi (%g)", float64(lo), float64(hi)))
	}
	f := Always{Inner: Atomic{Predicate: Between{Signal: SignalName(b.name), Min: lo, Max: hi}}}
	return CheckResult{
		formula: f, signalName: b.name,
		conditionDesc: fmt.Sprintf("between %g and %g", float64(lo), float64(hi)),
	}, nil
}

// NeverEquals produces G(¬(signal = value)).
func (b CheckSignalBuilder) NeverEquals(value PhysicalValue) CheckResult {
	f := Never(Equals{Signal: SignalName(b.name), Value: value})
	return CheckResult{
		formula: f, signalName: b.name,
		conditionDesc: fmt.Sprintf("!= %g", float64(value)),
	}
}

// Equals begins an equals(v).Always() chain.
func (b CheckSignalBuilder) Equals(value PhysicalValue) CheckSignalPredicate {
	f := Always{Inner: Atomic{Predicate: Equals{Signal: SignalName(b.name), Value: value}}}
	return CheckSignalPredicate{
		formula: f, signalName: b.name,
		conditionDesc: fmt.Sprintf("= %g", float64(value)),
	}
}

// SettlesBetween begins a settles_between(lo, hi).Within(ms) chain.
// An inverted range (lo > hi) is captured and surfaced from Within() so the
// fluent chain is unbroken.
func (b CheckSignalBuilder) SettlesBetween(lo, hi PhysicalValue) SettlesBuilder {
	sb := SettlesBuilder{signalName: b.name, lo: lo, hi: hi}
	if lo > hi {
		sb.rangeErr = validationError(fmt.Sprintf("settles_between: lo (%g) must be <= hi (%g)", float64(lo), float64(hi)))
	}
	return sb
}

// CheckSignalPredicate is an intermediate needing .Always() to finish.
type CheckSignalPredicate struct {
	formula       Formula
	signalName    string
	conditionDesc string
}

// Always confirms the predicate must hold at every time step.
func (p CheckSignalPredicate) Always() CheckResult {
	return CheckResult{
		formula: p.formula, signalName: p.signalName,
		conditionDesc: p.conditionDesc,
	}
}

// SettlesBuilder is an intermediate for SettlesBetween().Within().
type SettlesBuilder struct {
	signalName string
	lo, hi     PhysicalValue
	rangeErr   error // populated by SettlesBetween when lo > hi; surfaced from Within()
}

// Within completes the check: signal must settle between lo and hi within timeMs milliseconds.
func (b SettlesBuilder) Within(timeMs int64) (CheckResult, error) {
	if b.rangeErr != nil {
		return CheckResult{}, b.rangeErr
	}
	if timeMs < 0 {
		return CheckResult{}, validationError(fmt.Sprintf("time must be non-negative, got %d", timeMs))
	}
	if timeMs > math.MaxInt64/1000 {
		return CheckResult{}, validationError(fmt.Sprintf("time %d ms overflows microsecond conversion", timeMs))
	}
	f := AlwaysWithin(
		TimeBound{Microseconds: timeMs * 1000},
		Atomic{Predicate: Between{Signal: SignalName(b.signalName), Min: b.lo, Max: b.hi}},
	)
	return CheckResult{
		formula:    f,
		signalName: b.signalName,
		conditionDesc: fmt.Sprintf("between %g and %g within %dms",
			float64(b.lo), float64(b.hi), timeMs),
	}, nil
}

// ---------------------------------------------------------------------------
// When / Then causal check builders
// ---------------------------------------------------------------------------

// WhenSignalBuilder builds the trigger side of a causal check.
type WhenSignalBuilder struct {
	name string
}

// CheckWhen begins a causal when/then check.
func CheckWhen(name string) WhenSignalBuilder {
	return WhenSignalBuilder{name: name}
}

// Exceeds fires when signal exceeds value.
func (b WhenSignalBuilder) Exceeds(value PhysicalValue) WhenCondition {
	return WhenCondition{trigger: GreaterThan{Signal: SignalName(b.name), Value: value}}
}

// Equals fires when signal equals value.
func (b WhenSignalBuilder) Equals(value PhysicalValue) WhenCondition {
	return WhenCondition{trigger: Equals{Signal: SignalName(b.name), Value: value}}
}

// DropsBelow fires when signal drops below value.
func (b WhenSignalBuilder) DropsBelow(value PhysicalValue) WhenCondition {
	return WhenCondition{trigger: LessThan{Signal: SignalName(b.name), Value: value}}
}

// WhenCondition holds a trigger predicate and needs .Then() to continue.
type WhenCondition struct {
	trigger Predicate
}

// Then specifies the signal that must respond to the trigger.
func (c WhenCondition) Then(signalName string) ThenSignalBuilder {
	return ThenSignalBuilder{trigger: c.trigger, thenName: signalName}
}

// ThenSignalBuilder builds the response side of a when/then check.
type ThenSignalBuilder struct {
	trigger  Predicate
	thenName string
}

// Equals requires the then-signal to equal value.
func (b ThenSignalBuilder) Equals(value PhysicalValue) ThenCondition {
	return ThenCondition{
		trigger:    b.trigger,
		thenPred:   Equals{Signal: SignalName(b.thenName), Value: value},
		thenSignal: b.thenName,
		thenDesc:   fmt.Sprintf("= %g", float64(value)),
	}
}

// Exceeds requires the then-signal to exceed value.
func (b ThenSignalBuilder) Exceeds(value PhysicalValue) ThenCondition {
	return ThenCondition{
		trigger:    b.trigger,
		thenPred:   GreaterThan{Signal: SignalName(b.thenName), Value: value},
		thenSignal: b.thenName,
		thenDesc:   fmt.Sprintf("> %g", float64(value)),
	}
}

// StaysBetween requires the then-signal to stay between lo and hi.
// An inverted range (lo > hi) is captured and surfaced from Within() so the
// fluent chain is unbroken.
func (b ThenSignalBuilder) StaysBetween(lo, hi PhysicalValue) ThenCondition {
	tc := ThenCondition{
		trigger:    b.trigger,
		thenPred:   Between{Signal: SignalName(b.thenName), Min: lo, Max: hi},
		thenSignal: b.thenName,
		thenDesc:   fmt.Sprintf("between %g and %g", float64(lo), float64(hi)),
	}
	if lo > hi {
		tc.rangeErr = validationError(fmt.Sprintf("stays_between: lo (%g) must be <= hi (%g)", float64(lo), float64(hi)))
	}
	return tc
}

// ThenCondition holds trigger + response predicates and needs .Within() to finish.
type ThenCondition struct {
	trigger    Predicate
	thenPred   Predicate
	thenSignal string
	thenDesc   string
	rangeErr   error // populated by ThenSignalBuilder.StaysBetween when lo > hi
}

// Within completes the causal check: G(trigger → F≤t(response)).
func (c ThenCondition) Within(timeMs int64) (CheckResult, error) {
	if c.rangeErr != nil {
		return CheckResult{}, c.rangeErr
	}
	if timeMs < 0 {
		return CheckResult{}, validationError(fmt.Sprintf("time must be non-negative, got %d", timeMs))
	}
	if timeMs > math.MaxInt64/1000 {
		return CheckResult{}, validationError(fmt.Sprintf("time %d ms overflows microsecond conversion", timeMs))
	}
	us := TimeBound{Microseconds: timeMs * 1000}
	f := Always{Inner: Implies(
		Atomic{Predicate: c.trigger},
		EventuallyWithin(us, Atomic{Predicate: c.thenPred}),
	)}
	desc := ""
	if c.thenDesc != "" {
		desc = fmt.Sprintf("%s within %dms", c.thenDesc, timeMs)
	}
	return CheckResult{
		formula:       f,
		signalName:    c.thenSignal,
		conditionDesc: desc,
	}, nil
}
