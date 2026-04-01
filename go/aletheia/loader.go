package aletheia

import "fmt"

// Condition keyword sets for YAML and Excel loaders.
// Both loaders accept the same set of condition keywords and dispatch them
// through the same Check API builders.

var (
	simpleValueConditions   = map[string]bool{"never_exceeds": true, "never_below": true, "never_equals": true}
	simpleRangeConditions   = map[string]bool{"stays_between": true}
	simpleSettlesConditions = map[string]bool{"settles_between": true}
	simpleEqualsConditions  = map[string]bool{"equals": true}
	allSimpleConditions     = mergeConditions(simpleValueConditions, simpleRangeConditions, simpleSettlesConditions, simpleEqualsConditions)
	whenConditions          = map[string]bool{"exceeds": true, "equals": true, "drops_below": true}
	thenValueConditions     = map[string]bool{"equals": true, "exceeds": true}
	thenRangeConditions     = map[string]bool{"stays_between": true}
	allThenConditions       = mergeConditions(thenValueConditions, thenRangeConditions)
)

// mergeConditions returns the union of one or more condition sets.
func mergeConditions(sets ...map[string]bool) map[string]bool {
	result := make(map[string]bool)
	for _, s := range sets {
		for k := range s {
			result[k] = true
		}
	}
	return result
}

// dispatchSimple maps a simple single-value condition keyword to a Check API builder call.
// Handles: never_exceeds, never_below, never_equals.
func dispatchSimple(signal, condition string, value PhysicalValue) (CheckResult, error) {
	switch condition {
	case "never_exceeds":
		return CheckSignal(signal).NeverExceeds(value), nil
	case "never_below":
		return CheckSignal(signal).NeverBelow(value), nil
	case "never_equals":
		return CheckSignal(signal).NeverEquals(value), nil
	default:
		return CheckResult{}, fmt.Errorf("unknown simple condition: %q", condition)
	}
}

// dispatchWhen maps a when-condition keyword to a WhenCondition.
func dispatchWhen(builder WhenSignalBuilder, condition string, value PhysicalValue) (WhenCondition, error) {
	switch condition {
	case "exceeds":
		return builder.Exceeds(value), nil
	case "equals":
		return builder.Equals(value), nil
	case "drops_below":
		return builder.DropsBelow(value), nil
	default:
		return WhenCondition{}, fmt.Errorf("unknown when condition: %q", condition)
	}
}

// applyMetadata sets optional name and severity on a CheckResult.
func applyMetadata(r CheckResult, name, severity string) CheckResult {
	if name != "" {
		r = r.Named(name)
	}
	if severity != "" {
		r = r.Severity(severity)
	}
	return r
}

// checkCtx formats a check name as an error context string.
func checkCtx(name string) string {
	return fmt.Sprintf("Check '%s'", name)
}

// checkName extracts the check name from an entry, defaulting to "<unnamed>".
func checkName(name string) string {
	if name != "" {
		return name
	}
	return "<unnamed>"
}
