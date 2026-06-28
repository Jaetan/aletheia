// SPDX-FileCopyrightText: 2025 Nicolas Pelletier
// SPDX-License-Identifier: BSD-2-Clause

package aletheia

import (
	"fmt"
	"math"
	"math/big"
	"strings"
)

// descPart is one piece of a check's deferred condition description: literal
// text (isRat == false) or a threshold rendered lazily via the kernel formatℚ
// (isRat == true). Deferring keeps check *construction* infallible — only
// reading ConditionDesc() can surface a renderer error (the renderer is vocal
// when the GHC runtime is down) — so the fluent builder chain never fails
// mid-construction. Mirrors Rust's DescPart, C++'s deferred
// condition_desc_builder_, and Python's _desc_parts.
type descPart struct {
	lit   string
	rat   Rational
	isRat bool
}

func litPart(s string) descPart   { return descPart{lit: s} }
func ratPart(r Rational) descPart { return descPart{rat: r, isRat: true} }

// opDesc is an operator prefix followed by a single threshold, e.g. "<= " + r.
func opDesc(op string, r Rational) []descPart {
	return []descPart{litPart(op), ratPart(r)}
}

// betweenDesc renders "between {lo} and {hi}" with both bounds deferred to the
// kernel renderer.
func betweenDesc(lo, hi Rational) []descPart {
	return []descPart{litPart("between "), ratPart(lo), litPart(" and "), ratPart(hi)}
}

// withinDesc appends a " within {ms}ms" literal suffix to a deferred
// description (returns a fresh slice; never aliases parts).
func withinDesc(parts []descPart, timeMs int64) []descPart {
	out := make([]descPart, 0, len(parts)+1)
	out = append(out, parts...)
	return append(out, litPart(fmt.Sprintf(" within %dms", timeMs)))
}

// renderDesc renders a deferred description, delegating every threshold to the
// kernel formatℚ (the SSOT renderer) so the output is byte-identical to the Go
// formula printer and the other bindings — no local fallback. An empty parts
// renders to "" without touching the FFI.
//
// Returns an error if the kernel renderer is unavailable — the GHC runtime is
// not initialised (create an FFIBackend first); the renderer is vocal and never
// self-initialises.
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

// CheckResult is the terminal object produced by a check builder chain.
// It wraps an LTL formula with optional metadata for display/reporting.
// Metadata (name, severity) is not sent to the Agda core.
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

// ConditionDesc returns a human-readable description of the check condition,
// with thresholds rendered via the kernel formatℚ (the SSOT renderer; byte-
// identical to the formula printer and the Python / C++ / Rust check
// descriptions). Rendered lazily, so reading it requires a live GHC RTS (an
// FFIBackend) and returns an error when the runtime is down — check
// construction itself stays infallible.
func (r CheckResult) ConditionDesc() (string, error) { return renderDesc(r.descParts) }

// ratLessOrEqual reports whether a <= b for two rationals with positive
// denominators. It cross-multiplies through math/big so large operands cannot
// overflow int64 — the naive `a.num*b.den <= b.num*a.den` wraps for big values.
// This is LOCAL (not an FFI call): an overflow-safe rational comparison is
// trivial, so routing a <= test through the kernel would be overreach (the Go
// binding's deliberate deviation from the decimal SSOT, which covers
// parse / render only). Mirrors Rust's i128 cross-multiply in check.rs.
func ratLessOrEqual(a, b Rational) bool {
	left := new(big.Int).Mul(big.NewInt(a.Numerator), big.NewInt(b.Denominator))
	right := new(big.Int).Mul(big.NewInt(b.Numerator), big.NewInt(a.Denominator))
	return left.Cmp(right) <= 0
}

// ratStr formats a Rational for an inverted-range error message as plain
// num/den text (a bare integer when the denominator is 1). It does NOT use the
// kernel renderer: a validation-error path must not acquire an RTS dependency
// (the lo>hi rejection has to work — and be testable — without a live runtime).
func ratStr(r Rational) string {
	if r.Denominator == 1 {
		return fmt.Sprintf("%d", r.Numerator)
	}
	return fmt.Sprintf("%d/%d", r.Numerator, r.Denominator)
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
// The value is an exact [Rational] (use [IntRational] for an integer or the
// kernel [FromDecimal] for a decimal); construction is infallible.
func (b CheckSignalBuilder) NeverExceeds(value Rational) CheckResult {
	f := Always{Inner: Atomic{Predicate: LessThanOrEqual{Signal: SignalName(b.name), Value: value}}}
	return CheckResult{
		formula: f, signalName: b.name,
		descParts: opDesc("<= ", value),
	}
}

// NeverBelow produces G(signal >= value). The value is an exact [Rational];
// construction is infallible (see [CheckSignalBuilder.NeverExceeds]).
func (b CheckSignalBuilder) NeverBelow(value Rational) CheckResult {
	f := Always{Inner: Atomic{Predicate: GreaterThanOrEqual{Signal: SignalName(b.name), Value: value}}}
	return CheckResult{
		formula: f, signalName: b.name,
		descParts: opDesc(">= ", value),
	}
}

// StaysBetween produces G(lo <= signal <= hi).
// Returns an error if lo > hi (an inverted range is always false).
func (b CheckSignalBuilder) StaysBetween(lo, hi Rational) (CheckResult, error) {
	if !ratLessOrEqual(lo, hi) {
		return CheckResult{}, validationError(fmt.Sprintf("stays_between: lo (%s) must be <= hi (%s)", ratStr(lo), ratStr(hi)))
	}
	f := Always{Inner: Atomic{Predicate: Between{Signal: SignalName(b.name), Min: lo, Max: hi}}}
	return CheckResult{
		formula: f, signalName: b.name,
		descParts: betweenDesc(lo, hi),
	}, nil
}

// NeverEquals produces G(¬(signal = value)). The value is an exact [Rational];
// construction is infallible (see [CheckSignalBuilder.NeverExceeds]).
func (b CheckSignalBuilder) NeverEquals(value Rational) CheckResult {
	f := Never(Equals{Signal: SignalName(b.name), Value: value})
	return CheckResult{
		formula: f, signalName: b.name,
		descParts: opDesc("!= ", value),
	}
}

// Equals begins an equals(v).Always() chain. The value is an exact [Rational],
// so construction is infallible.
func (b CheckSignalBuilder) Equals(value Rational) CheckSignalPredicate {
	return CheckSignalPredicate{
		formula:    Always{Inner: Atomic{Predicate: Equals{Signal: SignalName(b.name), Value: value}}},
		signalName: b.name,
		descParts:  opDesc("= ", value),
	}
}

// SettlesBetween begins a settles_between(lo, hi).Within(ms) chain.
// An inverted range (lo > hi) is captured and surfaced from Within() so the
// fluent chain is unbroken.
func (b CheckSignalBuilder) SettlesBetween(lo, hi Rational) SettlesBuilder {
	sb := SettlesBuilder{signalName: b.name, lo: lo, hi: hi}
	if !ratLessOrEqual(lo, hi) {
		sb.rangeErr = validationError(fmt.Sprintf("settles_between: lo (%s) must be <= hi (%s)", ratStr(lo), ratStr(hi)))
	}
	return sb
}

// CheckSignalPredicate is an intermediate needing .Always() to finish.
type CheckSignalPredicate struct {
	formula    Formula
	signalName string
	descParts  []descPart
}

// Always confirms the predicate must hold at every time step.
func (p CheckSignalPredicate) Always() CheckResult {
	return CheckResult{
		formula: p.formula, signalName: p.signalName,
		descParts: p.descParts,
	}
}

// SettlesBuilder is an intermediate for SettlesBetween().Within().
type SettlesBuilder struct {
	signalName string
	lo, hi     Rational
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
	f := AlwaysWithin(
		TimeBound{Microseconds: timeMs * usPerMillisecond},
		Atomic{Predicate: Between{
			Signal: SignalName(b.signalName),
			Min:    b.lo,
			Max:    b.hi,
		}},
	)
	return CheckResult{
		formula:    f,
		signalName: b.signalName,
		descParts:  withinDesc(betweenDesc(b.lo, b.hi), timeMs),
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

// Exceeds fires when signal exceeds value. The value is an exact [Rational].
func (b WhenSignalBuilder) Exceeds(value Rational) WhenCondition {
	return WhenCondition{trigger: GreaterThan{Signal: SignalName(b.name), Value: value}}
}

// Equals fires when signal equals value. The value is an exact [Rational].
func (b WhenSignalBuilder) Equals(value Rational) WhenCondition {
	return WhenCondition{trigger: Equals{Signal: SignalName(b.name), Value: value}}
}

// DropsBelow fires when signal drops below value. The value is an exact [Rational].
func (b WhenSignalBuilder) DropsBelow(value Rational) WhenCondition {
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

// Equals requires the then-signal to equal value (an exact [Rational]).
func (b ThenSignalBuilder) Equals(value Rational) ThenCondition {
	return ThenCondition{
		trigger:       b.trigger,
		thenPred:      Equals{Signal: SignalName(b.thenName), Value: value},
		thenSignal:    b.thenName,
		thenDescParts: opDesc("= ", value),
	}
}

// Exceeds requires the then-signal to exceed value (an exact [Rational]).
func (b ThenSignalBuilder) Exceeds(value Rational) ThenCondition {
	return ThenCondition{
		trigger:       b.trigger,
		thenPred:      GreaterThan{Signal: SignalName(b.thenName), Value: value},
		thenSignal:    b.thenName,
		thenDescParts: opDesc("> ", value),
	}
}

// StaysBetween requires the then-signal to stay between lo and hi.
// An inverted range (lo > hi) is captured and surfaced from Within() so the
// fluent chain is unbroken.
func (b ThenSignalBuilder) StaysBetween(lo, hi Rational) ThenCondition {
	tc := ThenCondition{
		trigger:       b.trigger,
		thenPred:      Between{Signal: SignalName(b.thenName), Min: lo, Max: hi},
		thenSignal:    b.thenName,
		thenDescParts: betweenDesc(lo, hi),
	}
	if !ratLessOrEqual(lo, hi) {
		tc.rangeErr = validationError(fmt.Sprintf("stays_between: lo (%s) must be <= hi (%s)", ratStr(lo), ratStr(hi)))
	}
	return tc
}

// ThenCondition holds trigger + response predicates and needs .Within() to finish.
type ThenCondition struct {
	trigger       Predicate
	thenPred      Predicate
	thenSignal    string
	thenDescParts []descPart
	rangeErr      error // populated by ThenSignalBuilder.StaysBetween when lo > hi
}

// Within completes the causal check: G(trigger → F≤t(response)).
func (c ThenCondition) Within(timeMs int64) (CheckResult, error) {
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
	var desc []descPart
	if len(c.thenDescParts) > 0 {
		desc = withinDesc(c.thenDescParts, timeMs)
	}
	return CheckResult{
		formula:    f,
		signalName: c.thenSignal,
		descParts:  desc,
	}, nil
}
