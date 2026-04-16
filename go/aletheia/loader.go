package aletheia

import "fmt"

// Condition keyword sets shared by YAML, Excel, and any external loaders.
// Each loader dispatches condition keywords through the same builders, so the
// vocabulary lives here rather than being duplicated per file.

var (
	simpleValueConditions   = map[string]bool{"never_exceeds": true, "never_below": true, "never_equals": true}
	simpleRangeConditions   = map[string]bool{"stays_between": true}
	simpleSettlesConditions = map[string]bool{"settles_between": true}
	simpleEqualsConditions  = map[string]bool{"equals": true}
	allSimpleConditions     = mergeConditions(simpleValueConditions, simpleRangeConditions, simpleSettlesConditions, simpleEqualsConditions)
	whenConditions          = map[string]bool{"exceeds": true, "equals": true, "drops_below": true}
	allThenConditions       = map[string]bool{"equals": true, "exceeds": true, "stays_between": true}
)

// IsSimpleValueCondition reports whether s is a single-value condition keyword.
func IsSimpleValueCondition(s string) bool { return simpleValueConditions[s] }

// IsSimpleRangeCondition reports whether s is a range condition keyword.
func IsSimpleRangeCondition(s string) bool { return simpleRangeConditions[s] }

// IsSimpleSettlesCondition reports whether s is a settles condition keyword.
func IsSimpleSettlesCondition(s string) bool { return simpleSettlesConditions[s] }

// IsSimpleEqualsCondition reports whether s is an equals condition keyword.
func IsSimpleEqualsCondition(s string) bool { return simpleEqualsConditions[s] }

// IsSimpleCondition reports whether s is any simple condition keyword.
func IsSimpleCondition(s string) bool { return allSimpleConditions[s] }

// IsWhenCondition reports whether s is valid for the "when" leg of a when/then check.
func IsWhenCondition(s string) bool { return whenConditions[s] }

// IsThenCondition reports whether s is valid for the "then" leg of a when/then check.
func IsThenCondition(s string) bool { return allThenConditions[s] }

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

// DispatchSimple maps a simple single-value condition keyword to a Check API
// builder call. Handles never_exceeds, never_below, never_equals. Other simple
// conditions (stays_between, settles_between, equals) have their own shapes
// and are not dispatched through this helper. Exported for the Excel loader
// subpackage and any external plug-ins that accept the same vocabulary.
func DispatchSimple(signal, condition string, value PhysicalValue) (CheckResult, error) {
	switch condition {
	case "never_exceeds":
		return CheckSignal(signal).NeverExceeds(value), nil
	case "never_below":
		return CheckSignal(signal).NeverBelow(value), nil
	case "never_equals":
		return CheckSignal(signal).NeverEquals(value), nil
	default:
		return CheckResult{}, validationError(fmt.Sprintf("unknown simple condition: %q", condition))
	}
}

// DispatchWhen maps a when-condition keyword to a WhenCondition. Exported
// alongside [DispatchSimple] for the same reason — the Excel subpackage and
// external loaders share the vocabulary.
func DispatchWhen(builder WhenSignalBuilder, condition string, value PhysicalValue) (WhenCondition, error) {
	switch condition {
	case "exceeds":
		return builder.Exceeds(value), nil
	case "equals":
		return builder.Equals(value), nil
	case "drops_below":
		return builder.DropsBelow(value), nil
	default:
		return WhenCondition{}, validationError(fmt.Sprintf("unknown when condition: %q", condition))
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

// checkName extracts the check name from an entry, defaulting to "<unnamed>".
func checkName(name string) string {
	if name != "" {
		return name
	}
	return "<unnamed>"
}
