// SPDX-FileCopyrightText: 2025 Nicolas Pelletier
// SPDX-License-Identifier: BSD-2-Clause

package aletheia

import "fmt"

// The condition vocabulary every loader shares, the YAML one, the Excel one
// and anything outside this module that accepts the same words. Each keyword
// is written once, beside what it builds, so a word a loader accepts and no
// builder knows cannot exist: the set a loader asks about is the keys of the
// table the dispatcher reads.

// simpleValueBuilders are the conditions over one signal and one value.
var simpleValueBuilders = map[string]func(signal string, value Rational) CheckResult{
	"never_exceeds": func(signal string, value Rational) CheckResult {
		return CheckSignal(signal).NeverExceeds(value)
	},
	"never_below": func(signal string, value Rational) CheckResult {
		return CheckSignal(signal).NeverBelow(value)
	},
	"never_equals": func(signal string, value Rational) CheckResult {
		return CheckSignal(signal).NeverEquals(value)
	},
}

// whenBuilders are the conditions the leading half of a when-then check takes.
var whenBuilders = map[string]func(WhenSignalBuilder, Rational) WhenCondition{
	"exceeds":     WhenSignalBuilder.Exceeds,
	"equals":      WhenSignalBuilder.Equals,
	"drops_below": WhenSignalBuilder.DropsBelow,
}

// thenBuilders are the obligations the trailing half takes, each bounded in
// time. A builder reads the value slots its own condition uses and ignores the
// rest: a range takes the two bounds, the others take the single value.
var thenBuilders = map[string]func(b ThenSignalBuilder, value, lo, hi Rational, withinMs int64) (CheckResult, error){
	"equals": func(b ThenSignalBuilder, value, _, _ Rational, withinMs int64) (CheckResult, error) {
		return b.Equals(value).Within(withinMs)
	},
	"exceeds": func(b ThenSignalBuilder, value, _, _ Rational, withinMs int64) (CheckResult, error) {
		return b.Exceeds(value).Within(withinMs)
	},
	"stays_between": func(b ThenSignalBuilder, _, lo, hi Rational, withinMs int64) (CheckResult, error) {
		return b.StaysBetween(lo, hi).Within(withinMs)
	},
}

// The three conditions whose shapes each loader builds itself, having no
// single builder call to dispatch to: a range, a settling range and an
// equality. They are listed here so that every loader asks one vocabulary.
var (
	simpleRangeConditions   = map[string]bool{"stays_between": true}
	simpleSettlesConditions = map[string]bool{"settles_between": true}
	simpleEqualsConditions  = map[string]bool{"equals": true}
)

// IsSimpleValueCondition reports whether the word names a condition over one
// value.
func IsSimpleValueCondition(s string) bool { _, ok := simpleValueBuilders[s]; return ok }

// IsSimpleRangeCondition reports whether the word names a range condition.
func IsSimpleRangeCondition(s string) bool { return simpleRangeConditions[s] }

// IsSimpleSettlesCondition reports whether the word names a settling
// condition.
func IsSimpleSettlesCondition(s string) bool { return simpleSettlesConditions[s] }

// IsSimpleEqualsCondition reports whether the word names an equality.
func IsSimpleEqualsCondition(s string) bool { return simpleEqualsConditions[s] }

// IsSimpleCondition reports whether the word names any condition a check may
// carry on its own.
func IsSimpleCondition(s string) bool {
	return IsSimpleValueCondition(s) || simpleRangeConditions[s] ||
		simpleSettlesConditions[s] || simpleEqualsConditions[s]
}

// IsWhenCondition reports whether the word may lead a when-then check.
func IsWhenCondition(s string) bool { _, ok := whenBuilders[s]; return ok }

// IsThenCondition reports whether the word may close one.
func IsThenCondition(s string) bool { _, ok := thenBuilders[s]; return ok }

// DispatchSimple builds the check a single-value condition names. The other
// simple conditions have shapes of their own and each loader builds them.
func DispatchSimple(signal, condition string, value Rational) (CheckResult, error) {
	build, ok := simpleValueBuilders[condition]
	if !ok {
		return CheckResult{}, validationError(fmt.Sprintf("unknown simple condition: %q", condition))
	}
	return build(signal, value), nil
}

// DispatchWhen builds the leading half of a when-then check.
func DispatchWhen(builder WhenSignalBuilder, condition string, value Rational) (WhenCondition, error) {
	build, ok := whenBuilders[condition]
	if !ok {
		return WhenCondition{}, validationError(fmt.Sprintf("unknown when condition: %q", condition))
	}
	return build(builder, value), nil
}

// DispatchThen builds the trailing half, bounded in time.
func DispatchThen(builder ThenSignalBuilder, condition string, value, lo, hi Rational, withinMs int64) (CheckResult, error) {
	build, ok := thenBuilders[condition]
	if !ok {
		return CheckResult{}, validationError(fmt.Sprintf("unknown then condition: %q", condition))
	}
	return build(builder, value, lo, hi, withinMs)
}

// applyMetadata puts the optional name and severity on a check.
func applyMetadata(r CheckResult, name, severity string) CheckResult {
	if name != "" {
		r = r.Named(name)
	}
	if severity != "" {
		r = r.Severity(severity)
	}
	return r
}

// checkName is the name to report a check by, which is a placeholder when it
// has none.
func checkName(name string) string {
	if name != "" {
		return name
	}
	return "<unnamed>"
}
