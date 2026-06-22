// SPDX-FileCopyrightText: 2025 Nicolas Pelletier
// SPDX-License-Identifier: BSD-2-Clause

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

// firstError returns the first non-nil error, or nil. Used to thread a
// value-conversion failure through a fluent builder chain to its terminal
// (CheckResult, error) method.
func firstError(errs ...error) error {
	for _, e := range errs {
		if e != nil {
			return e
		}
	}
	return nil
}

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

// NeverExceeds produces G(signal <= value): the signal never goes above value,
// and value itself is allowed (inclusive — matches the Agda core's
// LessThanOrEqual and the dual NeverBelow's >=; "never exceeds 220" lets 220 pass).
// Returns an error if value is NaN, infinite, or overflows int64 when scaled
// to a rational (matching the Python and C++ bindings, which raise/throw rather
// than silently clamping a malformed value to 0/1).
func (b CheckSignalBuilder) NeverExceeds(value PhysicalValue) (CheckResult, error) {
	r, err := FloatToRational(float64(value))
	if err != nil {
		return CheckResult{}, err
	}
	f := Always{Inner: Atomic{Predicate: LessThanOrEqual{Signal: SignalName(b.name), Value: r}}}
	return CheckResult{
		formula: f, signalName: b.name,
		conditionDesc: fmt.Sprintf("<= %g", float64(value)),
	}, nil
}

// NeverBelow produces G(signal >= value).
// Returns an error if value cannot be converted to a rational (see [CheckSignalBuilder.NeverExceeds]).
func (b CheckSignalBuilder) NeverBelow(value PhysicalValue) (CheckResult, error) {
	r, err := FloatToRational(float64(value))
	if err != nil {
		return CheckResult{}, err
	}
	f := Always{Inner: Atomic{Predicate: GreaterThanOrEqual{Signal: SignalName(b.name), Value: r}}}
	return CheckResult{
		formula: f, signalName: b.name,
		conditionDesc: fmt.Sprintf(">= %g", float64(value)),
	}, nil
}

// StaysBetween produces G(lo <= signal <= hi).
// Returns an error if either bound cannot be converted to a rational, or if
// lo > hi (an inverted range is always false).
func (b CheckSignalBuilder) StaysBetween(lo, hi PhysicalValue) (CheckResult, error) {
	rLo, err := FloatToRational(float64(lo))
	if err != nil {
		return CheckResult{}, err
	}
	rHi, err := FloatToRational(float64(hi))
	if err != nil {
		return CheckResult{}, err
	}
	if lo > hi {
		return CheckResult{}, validationError(fmt.Sprintf("stays_between: lo (%g) must be <= hi (%g)", float64(lo), float64(hi)))
	}
	f := Always{Inner: Atomic{Predicate: Between{Signal: SignalName(b.name), Min: rLo, Max: rHi}}}
	return CheckResult{
		formula: f, signalName: b.name,
		conditionDesc: fmt.Sprintf("between %g and %g", float64(lo), float64(hi)),
	}, nil
}

// NeverEquals produces G(¬(signal = value)).
// Returns an error if value cannot be converted to a rational (see [CheckSignalBuilder.NeverExceeds]).
func (b CheckSignalBuilder) NeverEquals(value PhysicalValue) (CheckResult, error) {
	r, err := FloatToRational(float64(value))
	if err != nil {
		return CheckResult{}, err
	}
	f := Never(Equals{Signal: SignalName(b.name), Value: r})
	return CheckResult{
		formula: f, signalName: b.name,
		conditionDesc: fmt.Sprintf("!= %g", float64(value)),
	}, nil
}

// Equals begins an equals(v).Always() chain. A value that cannot be converted
// to a rational is captured and surfaced from [CheckSignalPredicate.Always] so
// the fluent chain is unbroken (mirroring the rangeErr pattern).
func (b CheckSignalBuilder) Equals(value PhysicalValue) CheckSignalPredicate {
	r, err := FloatToRational(float64(value))
	return CheckSignalPredicate{
		formula:       Always{Inner: Atomic{Predicate: Equals{Signal: SignalName(b.name), Value: r}}},
		signalName:    b.name,
		conditionDesc: fmt.Sprintf("= %g", float64(value)),
		valueErr:      err,
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
	valueErr      error // populated by Equals when the value is not convertible; surfaced from Always()
}

// Always confirms the predicate must hold at every time step.
// Returns the value-conversion error captured by [CheckSignalBuilder.Equals], if any.
func (p CheckSignalPredicate) Always() (CheckResult, error) {
	if p.valueErr != nil {
		return CheckResult{}, p.valueErr
	}
	return CheckResult{
		formula: p.formula, signalName: p.signalName,
		conditionDesc: p.conditionDesc,
	}, nil
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
	if timeMs > math.MaxInt64/usPerMillisecond {
		return CheckResult{}, validationError(fmt.Sprintf("time %d ms overflows microsecond conversion", timeMs))
	}
	rLo, err := FloatToRational(float64(b.lo))
	if err != nil {
		return CheckResult{}, err
	}
	rHi, err := FloatToRational(float64(b.hi))
	if err != nil {
		return CheckResult{}, err
	}
	f := AlwaysWithin(
		TimeBound{Microseconds: timeMs * usPerMillisecond},
		Atomic{Predicate: Between{
			Signal: SignalName(b.signalName),
			Min:    rLo,
			Max:    rHi,
		}},
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

// Exceeds fires when signal exceeds value. A non-convertible value is captured
// and surfaced from [ThenCondition.Within].
func (b WhenSignalBuilder) Exceeds(value PhysicalValue) WhenCondition {
	r, err := FloatToRational(float64(value))
	return WhenCondition{trigger: GreaterThan{Signal: SignalName(b.name), Value: r}, valueErr: err}
}

// Equals fires when signal equals value. A non-convertible value is captured
// and surfaced from [ThenCondition.Within].
func (b WhenSignalBuilder) Equals(value PhysicalValue) WhenCondition {
	r, err := FloatToRational(float64(value))
	return WhenCondition{trigger: Equals{Signal: SignalName(b.name), Value: r}, valueErr: err}
}

// DropsBelow fires when signal drops below value. A non-convertible value is
// captured and surfaced from [ThenCondition.Within].
func (b WhenSignalBuilder) DropsBelow(value PhysicalValue) WhenCondition {
	r, err := FloatToRational(float64(value))
	return WhenCondition{trigger: LessThan{Signal: SignalName(b.name), Value: r}, valueErr: err}
}

// WhenCondition holds a trigger predicate and needs .Then() to continue.
type WhenCondition struct {
	trigger  Predicate
	valueErr error // populated when the trigger value is not convertible; threaded to ThenCondition
}

// Then specifies the signal that must respond to the trigger.
func (c WhenCondition) Then(signalName string) ThenSignalBuilder {
	return ThenSignalBuilder{trigger: c.trigger, thenName: signalName, valueErr: c.valueErr}
}

// ThenSignalBuilder builds the response side of a when/then check.
type ThenSignalBuilder struct {
	trigger  Predicate
	thenName string
	valueErr error // carried from the when-clause; combined with the then-value error
}

// Equals requires the then-signal to equal value.
func (b ThenSignalBuilder) Equals(value PhysicalValue) ThenCondition {
	r, err := FloatToRational(float64(value))
	return ThenCondition{
		trigger:    b.trigger,
		thenPred:   Equals{Signal: SignalName(b.thenName), Value: r},
		thenSignal: b.thenName,
		thenDesc:   fmt.Sprintf("= %g", float64(value)),
		valueErr:   firstError(b.valueErr, err),
	}
}

// Exceeds requires the then-signal to exceed value.
func (b ThenSignalBuilder) Exceeds(value PhysicalValue) ThenCondition {
	r, err := FloatToRational(float64(value))
	return ThenCondition{
		trigger:    b.trigger,
		thenPred:   GreaterThan{Signal: SignalName(b.thenName), Value: r},
		thenSignal: b.thenName,
		thenDesc:   fmt.Sprintf("> %g", float64(value)),
		valueErr:   firstError(b.valueErr, err),
	}
}

// StaysBetween requires the then-signal to stay between lo and hi.
// An inverted range (lo > hi) or a non-convertible bound is captured and
// surfaced from Within() so the fluent chain is unbroken.
func (b ThenSignalBuilder) StaysBetween(lo, hi PhysicalValue) ThenCondition {
	rLo, loErr := FloatToRational(float64(lo))
	rHi, hiErr := FloatToRational(float64(hi))
	tc := ThenCondition{
		trigger:    b.trigger,
		thenPred:   Between{Signal: SignalName(b.thenName), Min: rLo, Max: rHi},
		thenSignal: b.thenName,
		thenDesc:   fmt.Sprintf("between %g and %g", float64(lo), float64(hi)),
		valueErr:   firstError(b.valueErr, loErr, hiErr),
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
	valueErr   error // populated when a when/then value is not convertible to a rational
}

// Within completes the causal check: G(trigger → F≤t(response)).
func (c ThenCondition) Within(timeMs int64) (CheckResult, error) {
	if c.valueErr != nil {
		return CheckResult{}, c.valueErr
	}
	if c.rangeErr != nil {
		return CheckResult{}, c.rangeErr
	}
	if timeMs < 0 {
		return CheckResult{}, validationError(fmt.Sprintf("time must be non-negative, got %d", timeMs))
	}
	if timeMs > math.MaxInt64/usPerMillisecond {
		return CheckResult{}, validationError(fmt.Sprintf("time %d ms overflows microsecond conversion", timeMs))
	}
	us := TimeBound{Microseconds: timeMs * usPerMillisecond}
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
