// SPDX-FileCopyrightText: 2025 Nicolas Pelletier
// SPDX-License-Identifier: BSD-2-Clause

package aletheia

import "fmt"

// The condition vocabulary every loader shares, the YAML one, the Excel one
// and anything outside this module that accepts the same words. Each keyword
// is written once beside what it builds, and the builder asks its loader for
// the slots its own condition reads, so no loader decides that a second time.
// A condition added to a table below reaches every loader untouched; one that
// needs a slot no loader answers cannot be added until the interface grows a
// method, which every loader must implement before it compiles again.

// SimpleValues is what a loader is asked for when a condition a check carries
// on its own is built: the single value it compares against, the pair of
// bounds it holds between, or the time bound. Each is answered from that
// loader's own key or column, or refused in that loader's own words naming
// what is missing, and a builder calls only what its condition reads.
type SimpleValues interface {
	Value() (Rational, error)
	Range() (lo, hi Rational, err error)
	// Within is read by the settling condition alone, which is why the time
	// bound is a slot here and a parameter in the then half, where every
	// obligation is bounded.
	Within() (TimeBound, error)
}

// ThenValues is the same for the obligation a when-then check closes with,
// less the time bound, which DispatchThen takes directly.
type ThenValues interface {
	Value() (Rational, error)
	Range() (lo, hi Rational, err error)
}

// simpleBuilders are the conditions a check carries on its own.
var simpleBuilders = map[string]func(signal string, v SimpleValues) (CheckResult, error){
	"never_exceeds": func(signal string, v SimpleValues) (CheckResult, error) {
		value, err := v.Value()
		if err != nil {
			return CheckResult{}, err
		}
		return CheckSignal(signal).NeverExceeds(value)
	},
	"never_below": func(signal string, v SimpleValues) (CheckResult, error) {
		value, err := v.Value()
		if err != nil {
			return CheckResult{}, err
		}
		return CheckSignal(signal).NeverBelow(value)
	},
	"never_equals": func(signal string, v SimpleValues) (CheckResult, error) {
		value, err := v.Value()
		if err != nil {
			return CheckResult{}, err
		}
		return CheckSignal(signal).NeverEquals(value)
	},
	"equals": func(signal string, v SimpleValues) (CheckResult, error) {
		value, err := v.Value()
		if err != nil {
			return CheckResult{}, err
		}
		return CheckSignal(signal).Equals(value).Always()
	},
	"stays_between": func(signal string, v SimpleValues) (CheckResult, error) {
		lo, hi, err := v.Range()
		if err != nil {
			return CheckResult{}, err
		}
		return CheckSignal(signal).StaysBetween(lo, hi)
	},
	"settles_between": func(signal string, v SimpleValues) (CheckResult, error) {
		lo, hi, err := v.Range()
		if err != nil {
			return CheckResult{}, err
		}
		within, err := v.Within()
		if err != nil {
			return CheckResult{}, err
		}
		return CheckSignal(signal).SettlesBetween(lo, hi).Within(within)
	},
}

// whenBuilders are the conditions the leading half of a when-then check takes.
// All three read one value, which is why the leading half has no slots
// interface: the dispatcher takes the value directly.
var whenBuilders = map[string]func(WhenSignalBuilder, Rational) WhenCondition{
	"exceeds":     WhenSignalBuilder.Exceeds,
	"equals":      WhenSignalBuilder.Equals,
	"drops_below": WhenSignalBuilder.DropsBelow,
}

// thenBuilders are the obligations the trailing half takes, each bounded in
// time.
var thenBuilders = map[string]func(b ThenSignalBuilder, v ThenValues, within TimeBound) (CheckResult, error){
	"equals": func(b ThenSignalBuilder, v ThenValues, within TimeBound) (CheckResult, error) {
		value, err := v.Value()
		if err != nil {
			return CheckResult{}, err
		}
		return b.Equals(value).Within(within)
	},
	"exceeds": func(b ThenSignalBuilder, v ThenValues, within TimeBound) (CheckResult, error) {
		value, err := v.Value()
		if err != nil {
			return CheckResult{}, err
		}
		return b.Exceeds(value).Within(within)
	},
	"stays_between": func(b ThenSignalBuilder, v ThenValues, within TimeBound) (CheckResult, error) {
		lo, hi, err := v.Range()
		if err != nil {
			return CheckResult{}, err
		}
		return b.StaysBetween(lo, hi).Within(within)
	},
}

// IsSimpleCondition reports whether the word names a condition a check may
// carry on its own.
func IsSimpleCondition(s string) bool { _, ok := simpleBuilders[s]; return ok }

// IsWhenCondition reports whether the word may lead a when-then check.
func IsWhenCondition(s string) bool { _, ok := whenBuilders[s]; return ok }

// IsThenCondition reports whether the word may close one.
func IsThenCondition(s string) bool { _, ok := thenBuilders[s]; return ok }

// DispatchSimple builds the check a condition names, asking the loader for the
// slots that condition reads.
func DispatchSimple(signal, condition string, values SimpleValues) (CheckResult, error) {
	build, ok := simpleBuilders[condition]
	if !ok {
		return CheckResult{}, validationError(fmt.Sprintf("unknown simple condition: %q", condition))
	}
	return build(signal, values)
}

// DispatchWhen builds the leading half of a when-then check.
func DispatchWhen(builder WhenSignalBuilder, condition string, value Rational) (WhenCondition, error) {
	build, ok := whenBuilders[condition]
	if !ok {
		return WhenCondition{}, validationError(fmt.Sprintf("unknown when condition: %q", condition))
	}
	return build(builder, value), nil
}

// DispatchThen builds the trailing half, bounded in time, asking the loader
// for the slots the obligation reads.
func DispatchThen(builder ThenSignalBuilder, condition string, values ThenValues, within TimeBound) (CheckResult, error) {
	build, ok := thenBuilders[condition]
	if !ok {
		return CheckResult{}, validationError(fmt.Sprintf("unknown then condition: %q", condition))
	}
	return build(builder, values, within)
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
