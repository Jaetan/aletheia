// SPDX-FileCopyrightText: 2025 Nicolas Pelletier
// SPDX-License-Identifier: BSD-2-Clause

package aletheia

import (
	"fmt"
	"slices"
	"strings"
)

// descPart is one piece of a check's condition description: literal text, or
// a threshold rendered later by the kernel's rational renderer, when
// ConditionDesc asks. Rust (DescPart), C++ (condition_desc_) and Python
// (_desc_parts) defer the same way.
type descPart struct {
	lit   string
	rat   Rational
	isRat bool
}

func litPart(s string) descPart   { return descPart{lit: s} }
func ratPart(r Rational) descPart { return descPart{rat: r, isRat: true} }

// opDesc is an operator prefix followed by one threshold, such as "<= " r.
func opDesc(op string, r Rational) []descPart {
	return []descPart{litPart(op), ratPart(r)}
}

// betweenDesc is "between lo and hi" with both bounds deferred.
func betweenDesc(lo, hi Rational) []descPart {
	return []descPart{litPart("between "), ratPart(lo), litPart(" and "), ratPart(hi)}
}

// withinDesc appends " within {t}µs" to a copy of parts.
func withinDesc(parts []descPart, t TimeBound) []descPart {
	return slices.Concat(parts, []descPart{litPart(fmt.Sprintf(" within %dµs", t.Microseconds))})
}

// renderDesc renders a description, sending every threshold to the kernel
// renderer so the text is byte-identical to the formula printer and to the
// other bindings. Empty parts render to "" without reaching the FFI. The
// error is the renderer's: the GHC runtime is not up, and the renderer never
// starts it.
func renderDesc(parts []descPart) (string, error) {
	var b strings.Builder
	for _, p := range parts {
		if !p.isRat {
			b.WriteString(p.lit)
			continue
		}
		s, err := formatRational(p.rat)
		if err != nil {
			return "", err
		}
		b.WriteString(s)
	}
	return b.String(), nil
}

// CheckResult is what a check builder chain produces: an LTL formula with
// metadata for display and reporting. The metadata is not sent to the core.
//
// Each chain's finishing call hands the formula it made to the kernel's
// property parse, which refuses a zero denominator, a range whose minimum is
// above its maximum, a time bound past its limit and a signal name that is no
// identifier, with the reason set_properties would give. The parse needs the
// GHC runtime up ([StartRuntime] or a backend), so building a check while it
// is down fails with [ErrFFI].
type CheckResult struct {
	formula    Formula
	name       string
	severity   string
	signalName string
	descParts  []descPart
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

// ConditionDesc returns the condition in words, thresholds rendered by the
// kernel renderer, so it needs the GHC runtime up ([StartRuntime] or a
// backend) and returns the renderer's error without it.
func (r CheckResult) ConditionDesc() (string, error) { return renderDesc(r.descParts) }

// checked is the check over f, once the kernel's property parse reads f.
func checked(f Formula, signalName string, parts []descPart) (CheckResult, error) {
	if err := checkFormula(f); err != nil {
		return CheckResult{}, err
	}
	return CheckResult{formula: f, signalName: signalName, descParts: parts}, nil
}

// CheckSignalBuilder builds single-signal checks.
type CheckSignalBuilder struct {
	name string
}

// CheckSignal begins a single-signal check.
func CheckSignal(name string) CheckSignalBuilder {
	return CheckSignalBuilder{name: name}
}

// NeverExceeds produces G(signal <= value): the value itself is allowed, as
// in the core's LessThanOrEqual and in NeverBelow's >=. The value is an exact
// [Rational] ([IntRational] for an integer, [FromDecimal] for a decimal).
func (b CheckSignalBuilder) NeverExceeds(value Rational) (CheckResult, error) {
	f := Always{Inner: Atomic{Predicate: LessThanOrEqual{Signal: SignalName(b.name), Value: value}}}
	return checked(f, b.name, opDesc("<= ", value))
}

// NeverBelow produces G(signal >= value).
func (b CheckSignalBuilder) NeverBelow(value Rational) (CheckResult, error) {
	f := Always{Inner: Atomic{Predicate: GreaterThanOrEqual{Signal: SignalName(b.name), Value: value}}}
	return checked(f, b.name, opDesc(">= ", value))
}

// StaysBetween produces G(lo <= signal <= hi).
func (b CheckSignalBuilder) StaysBetween(lo, hi Rational) (CheckResult, error) {
	f := Always{Inner: Atomic{Predicate: Between{Signal: SignalName(b.name), Min: lo, Max: hi}}}
	return checked(f, b.name, betweenDesc(lo, hi))
}

// NeverEquals produces G(not (signal = value)).
func (b CheckSignalBuilder) NeverEquals(value Rational) (CheckResult, error) {
	return checked(Never(Equals{Signal: SignalName(b.name), Value: value}), b.name, opDesc("!= ", value))
}

// Equals begins an Equals(v).Always() chain, which Always checks.
func (b CheckSignalBuilder) Equals(value Rational) CheckSignalPredicate {
	return CheckSignalPredicate{
		formula:    Always{Inner: Atomic{Predicate: Equals{Signal: SignalName(b.name), Value: value}}},
		signalName: b.name,
		descParts:  opDesc("= ", value),
	}
}

// SettlesBetween begins a SettlesBetween(lo, hi).Within(t) chain, which
// Within checks, so the chain never breaks.
func (b CheckSignalBuilder) SettlesBetween(lo, hi Rational) SettlesBuilder {
	return SettlesBuilder{signalName: b.name, lo: lo, hi: hi}
}

// CheckSignalPredicate is an intermediate that needs Always to finish.
type CheckSignalPredicate struct {
	formula    Formula
	signalName string
	descParts  []descPart
}

// Always completes the check: the predicate holds at every step.
func (p CheckSignalPredicate) Always() (CheckResult, error) {
	return checked(p.formula, p.signalName, p.descParts)
}

// SettlesBuilder is the intermediate of SettlesBetween().Within().
type SettlesBuilder struct {
	signalName string
	lo, hi     Rational
}

// Within completes the check: the signal settles between lo and hi within
// the bound.
func (b SettlesBuilder) Within(bound TimeBound) (CheckResult, error) {
	f := MetricAlways{Bound: bound, Inner: Atomic{Predicate: Between{Signal: SignalName(b.signalName), Min: b.lo, Max: b.hi}}}
	return checked(f, b.signalName, withinDesc(betweenDesc(b.lo, b.hi), bound))
}

// WhenSignalBuilder builds the trigger side of a causal check.
type WhenSignalBuilder struct {
	name string
}

// CheckWhen begins a causal when/then check.
func CheckWhen(name string) WhenSignalBuilder {
	return WhenSignalBuilder{name: name}
}

// Exceeds fires when the signal exceeds value, an exact [Rational].
func (b WhenSignalBuilder) Exceeds(value Rational) WhenCondition {
	return WhenCondition{trigger: GreaterThan{Signal: SignalName(b.name), Value: value}}
}

// Equals fires when the signal equals value, an exact [Rational].
func (b WhenSignalBuilder) Equals(value Rational) WhenCondition {
	return WhenCondition{trigger: Equals{Signal: SignalName(b.name), Value: value}}
}

// DropsBelow fires when the signal drops below value, an exact [Rational].
func (b WhenSignalBuilder) DropsBelow(value Rational) WhenCondition {
	return WhenCondition{trigger: LessThan{Signal: SignalName(b.name), Value: value}}
}

// WhenCondition holds the trigger and needs Then to continue.
type WhenCondition struct {
	trigger Predicate
}

// Then names the signal that must respond to the trigger.
func (c WhenCondition) Then(signalName string) ThenSignalBuilder {
	return ThenSignalBuilder{trigger: c.trigger, thenName: signalName}
}

// ThenSignalBuilder builds the response side of a when/then check.
type ThenSignalBuilder struct {
	trigger  Predicate
	thenName string
}

// Equals requires the then-signal to equal value, an exact [Rational].
func (b ThenSignalBuilder) Equals(value Rational) ThenCondition {
	return ThenCondition{
		trigger:       b.trigger,
		thenPred:      Equals{Signal: SignalName(b.thenName), Value: value},
		thenSignal:    b.thenName,
		thenDescParts: opDesc("= ", value),
	}
}

// Exceeds requires the then-signal to exceed value, an exact [Rational].
func (b ThenSignalBuilder) Exceeds(value Rational) ThenCondition {
	return ThenCondition{
		trigger:       b.trigger,
		thenPred:      GreaterThan{Signal: SignalName(b.thenName), Value: value},
		thenSignal:    b.thenName,
		thenDescParts: opDesc("> ", value),
	}
}

// StaysBetween requires the then-signal to stay between lo and hi, which
// Within checks, so the chain never breaks.
func (b ThenSignalBuilder) StaysBetween(lo, hi Rational) ThenCondition {
	return ThenCondition{
		trigger:       b.trigger,
		thenPred:      Between{Signal: SignalName(b.thenName), Min: lo, Max: hi},
		thenSignal:    b.thenName,
		thenDescParts: betweenDesc(lo, hi),
	}
}

// ThenCondition holds the trigger and the response and needs Within to finish.
type ThenCondition struct {
	trigger       Predicate
	thenPred      Predicate
	thenSignal    string
	thenDescParts []descPart
}

// Within completes the causal check: G(trigger implies F within t
// (response)). It checks the whole formula, trigger included.
func (c ThenCondition) Within(bound TimeBound) (CheckResult, error) {
	f := Always{Inner: Implies(
		Atomic{Predicate: c.trigger},
		MetricEventually{Bound: bound, Inner: Atomic{Predicate: c.thenPred}},
	)}
	return checked(f, c.thenSignal, withinDesc(c.thenDescParts, bound))
}
