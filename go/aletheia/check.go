// SPDX-FileCopyrightText: 2025 Nicolas Pelletier
// SPDX-License-Identifier: BSD-2-Clause

package aletheia

import (
	"fmt"
	"math"
	"math/big"
	"strings"
)

// descPart is one piece of a check's condition description: literal text, or
// a threshold rendered later by the kernel's rational renderer. Deferring the
// rendering keeps check construction infallible; only ConditionDesc can fail,
// when the GHC runtime is down. Rust (DescPart), C++ (condition_desc_builder_)
// and Python (_desc_parts) defer the same way.
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

// withinDesc appends " within {ms}ms" to a copy of parts.
func withinDesc(parts []descPart, timeMs int64) []descPart {
	out := make([]descPart, 0, len(parts)+1)
	out = append(out, parts...)
	return append(out, litPart(fmt.Sprintf(" within %dms", timeMs)))
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
// kernel renderer, so it needs a live GHC runtime (an FFIBackend) and returns
// the renderer's error without one. Construction never fails; only this does.
func (r CheckResult) ConditionDesc() (string, error) { return renderDesc(r.descParts) }

// ratLessOrEqual reports a <= b for rationals with positive denominators. It
// cross-multiplies through math/big, since the int64 products overflow for
// large operands. Local on purpose: the comparison is trivial and the kernel
// owns parsing and rendering only. The Rust Rational ordering in types.rs
// does the same through i128.
func ratLessOrEqual(a, b Rational) bool {
	left := new(big.Int).Mul(big.NewInt(a.Numerator), big.NewInt(b.Denominator))
	right := new(big.Int).Mul(big.NewInt(b.Numerator), big.NewInt(a.Denominator))
	return left.Cmp(right) <= 0
}

// ratStr writes a Rational as num/den, or the bare integer when den is 1,
// for the inverted-range message. It does not use the kernel renderer: a
// validation error must not need a live runtime.
func ratStr(r Rational) string {
	if r.Denominator == 1 {
		return fmt.Sprintf("%d", r.Numerator)
	}
	return fmt.Sprintf("%d/%d", r.Numerator, r.Denominator)
}

// requireOrdered is the error for an inverted range, nil when lo <= hi; op
// names the builder in the message.
func requireOrdered(op string, lo, hi Rational) error {
	if ratLessOrEqual(lo, hi) {
		return nil
	}
	return validationError(fmt.Sprintf("%s: lo (%s) must be <= hi (%s)", op, ratStr(lo), ratStr(hi)))
}

// timeBoundMs converts a millisecond bound to the kernel's microseconds,
// refusing a negative value and one whose conversion overflows int64.
func timeBoundMs(timeMs int64) (TimeBound, error) {
	if timeMs < 0 {
		return TimeBound{}, validationError(fmt.Sprintf("time must be non-negative, got %d", timeMs))
	}
	if timeMs > math.MaxInt64/usPerMillisecond {
		return TimeBound{}, validationError(fmt.Sprintf("time %d ms overflows microsecond conversion", timeMs))
	}
	return TimeBound{Microseconds: timeMs * usPerMillisecond}, nil
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
// [Rational] ([IntRational] for an integer, [FromDecimal] for a decimal);
// construction is infallible.
func (b CheckSignalBuilder) NeverExceeds(value Rational) CheckResult {
	f := Always{Inner: Atomic{Predicate: LessThanOrEqual{Signal: SignalName(b.name), Value: value}}}
	return CheckResult{
		formula: f, signalName: b.name,
		descParts: opDesc("<= ", value),
	}
}

// NeverBelow produces G(signal >= value); construction is infallible.
func (b CheckSignalBuilder) NeverBelow(value Rational) CheckResult {
	f := Always{Inner: Atomic{Predicate: GreaterThanOrEqual{Signal: SignalName(b.name), Value: value}}}
	return CheckResult{
		formula: f, signalName: b.name,
		descParts: opDesc(">= ", value),
	}
}

// StaysBetween produces G(lo <= signal <= hi), or an error when lo > hi.
func (b CheckSignalBuilder) StaysBetween(lo, hi Rational) (CheckResult, error) {
	if err := requireOrdered("stays_between", lo, hi); err != nil {
		return CheckResult{}, err
	}
	f := Always{Inner: Atomic{Predicate: Between{Signal: SignalName(b.name), Min: lo, Max: hi}}}
	return CheckResult{
		formula: f, signalName: b.name,
		descParts: betweenDesc(lo, hi),
	}, nil
}

// NeverEquals produces G(not (signal = value)); construction is infallible.
func (b CheckSignalBuilder) NeverEquals(value Rational) CheckResult {
	f := Never(Equals{Signal: SignalName(b.name), Value: value})
	return CheckResult{
		formula: f, signalName: b.name,
		descParts: opDesc("!= ", value),
	}
}

// Equals begins an Equals(v).Always() chain; construction is infallible.
func (b CheckSignalBuilder) Equals(value Rational) CheckSignalPredicate {
	return CheckSignalPredicate{
		formula:    Always{Inner: Atomic{Predicate: Equals{Signal: SignalName(b.name), Value: value}}},
		signalName: b.name,
		descParts:  opDesc("= ", value),
	}
}

// SettlesBetween begins a SettlesBetween(lo, hi).Within(ms) chain. An
// inverted range is kept and surfaced by Within, so the chain never breaks.
func (b CheckSignalBuilder) SettlesBetween(lo, hi Rational) SettlesBuilder {
	return SettlesBuilder{signalName: b.name, lo: lo, hi: hi, rangeErr: requireOrdered("settles_between", lo, hi)}
}

// CheckSignalPredicate is an intermediate that needs Always to finish.
type CheckSignalPredicate struct {
	formula    Formula
	signalName string
	descParts  []descPart
}

// Always completes the check: the predicate holds at every step.
func (p CheckSignalPredicate) Always() CheckResult {
	return CheckResult{
		formula: p.formula, signalName: p.signalName,
		descParts: p.descParts,
	}
}

// SettlesBuilder is the intermediate of SettlesBetween().Within().
type SettlesBuilder struct {
	signalName string
	lo, hi     Rational
	rangeErr   error // set by SettlesBetween when lo > hi, surfaced by Within
}

// Within completes the check: the signal settles between lo and hi within
// timeMs milliseconds.
func (b SettlesBuilder) Within(timeMs int64) (CheckResult, error) {
	if b.rangeErr != nil {
		return CheckResult{}, b.rangeErr
	}
	bound, err := timeBoundMs(timeMs)
	if err != nil {
		return CheckResult{}, err
	}
	f := AlwaysWithin(bound, Atomic{Predicate: Between{Signal: SignalName(b.signalName), Min: b.lo, Max: b.hi}})
	return CheckResult{
		formula:    f,
		signalName: b.signalName,
		descParts:  withinDesc(betweenDesc(b.lo, b.hi), timeMs),
	}, nil
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

// StaysBetween requires the then-signal to stay between lo and hi. An
// inverted range is kept and surfaced by Within, so the chain never breaks.
func (b ThenSignalBuilder) StaysBetween(lo, hi Rational) ThenCondition {
	return ThenCondition{
		trigger:       b.trigger,
		thenPred:      Between{Signal: SignalName(b.thenName), Min: lo, Max: hi},
		thenSignal:    b.thenName,
		thenDescParts: betweenDesc(lo, hi),
		rangeErr:      requireOrdered("stays_between", lo, hi),
	}
}

// ThenCondition holds the trigger and the response and needs Within to finish.
type ThenCondition struct {
	trigger       Predicate
	thenPred      Predicate
	thenSignal    string
	thenDescParts []descPart
	rangeErr      error // set by StaysBetween when lo > hi, surfaced by Within
}

// Within completes the causal check: G(trigger implies F within t (response)).
func (c ThenCondition) Within(timeMs int64) (CheckResult, error) {
	if c.rangeErr != nil {
		return CheckResult{}, c.rangeErr
	}
	bound, err := timeBoundMs(timeMs)
	if err != nil {
		return CheckResult{}, err
	}
	f := Always{Inner: Implies(
		Atomic{Predicate: c.trigger},
		EventuallyWithin(bound, Atomic{Predicate: c.thenPred}),
	)}
	return CheckResult{
		formula:    f,
		signalName: c.thenSignal,
		descParts:  withinDesc(c.thenDescParts, timeMs),
	}, nil
}
