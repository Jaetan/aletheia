package aletheia

import (
	"fmt"
	"strings"
)

// PropertyDiagnostic holds metadata auto-derived from a formula for violation enrichment.
type PropertyDiagnostic struct {
	Signals     []SignalName // all signals referenced in the formula
	FormulaDesc string       // human-readable formula representation
}

// ViolationEnrichment carries human-readable context added to violations.
type ViolationEnrichment struct {
	Signals        map[SignalName]PhysicalValue // actual values from frame (nil if extraction failed)
	FormulaDesc    string
	EnrichedReason string
}

// BuildDiagnostic creates a PropertyDiagnostic from a formula. Always succeeds.
func BuildDiagnostic(f Formula) PropertyDiagnostic {
	return PropertyDiagnostic{
		Signals:     CollectSignals(f),
		FormulaDesc: FormatFormula(f),
	}
}

// FormatFormula returns a human-readable representation of an LTL formula.
func FormatFormula(f Formula) string {
	switch v := f.(type) {
	case Atomic:
		return formatPredicate(v.Predicate)
	case Not:
		return "not(" + FormatFormula(v.Inner) + ")"
	case And:
		return FormatFormula(v.Left) + " and " + FormatFormula(v.Right)
	case Or:
		return FormatFormula(v.Left) + " or " + FormatFormula(v.Right)
	case Next:
		return "next(" + FormatFormula(v.Inner) + ")"
	case Always:
		// Detect Never pattern: Always{Not{Atomic{p}}}
		if n, ok := v.Inner.(Not); ok {
			if a, ok := n.Inner.(Atomic); ok {
				return "never " + formatPredicate(a.Predicate)
			}
		}
		return "always(" + FormatFormula(v.Inner) + ")"
	case Eventually:
		return "eventually(" + FormatFormula(v.Inner) + ")"
	case Until:
		return FormatFormula(v.Left) + " until " + FormatFormula(v.Right)
	case Release:
		return FormatFormula(v.Left) + " release " + FormatFormula(v.Right)
	case MetricAlways:
		return "always within " + formatTimebound(v.Bound) + "(" + FormatFormula(v.Inner) + ")"
	case MetricEventually:
		return "eventually within " + formatTimebound(v.Bound) + "(" + FormatFormula(v.Inner) + ")"
	case MetricUntil:
		return FormatFormula(v.Left) + " until within " + formatTimebound(v.Bound) + " " + FormatFormula(v.Right)
	case MetricRelease:
		return FormatFormula(v.Left) + " release within " + formatTimebound(v.Bound) + " " + FormatFormula(v.Right)
	default:
		return "<unknown>"
	}
}

// formatPredicate returns a human-readable representation of a predicate.
func formatPredicate(p Predicate) string {
	switch v := p.(type) {
	case Equals:
		return fmt.Sprintf("%s = %s", v.Signal, formatValue(float64(v.Value)))
	case LessThan:
		return fmt.Sprintf("%s < %s", v.Signal, formatValue(float64(v.Value)))
	case GreaterThan:
		return fmt.Sprintf("%s > %s", v.Signal, formatValue(float64(v.Value)))
	case LessThanOrEqual:
		return fmt.Sprintf("%s <= %s", v.Signal, formatValue(float64(v.Value)))
	case GreaterThanOrEqual:
		return fmt.Sprintf("%s >= %s", v.Signal, formatValue(float64(v.Value)))
	case Between:
		return fmt.Sprintf("%s <= %s <= %s", formatValue(float64(v.Min)), v.Signal, formatValue(float64(v.Max)))
	case ChangedBy:
		return fmt.Sprintf("|Δ%s| > %s", v.Signal, formatValue(float64(v.Delta)))
	default:
		return "<unknown predicate>"
	}
}

// formatValue formats a float64 without trailing zeros.
func formatValue(v float64) string {
	s := fmt.Sprintf("%g", v)
	return s
}

// formatTimebound formats a Timestamp as a human-readable time bound.
func formatTimebound(t Timestamp) string {
	us := t.Microseconds
	if us%1000000 == 0 {
		return fmt.Sprintf("%ds ", us/1000000)
	}
	if us%1000 == 0 {
		return fmt.Sprintf("%dms ", us/1000)
	}
	return fmt.Sprintf("%dμs ", us)
}

// CollectSignals returns all signal names referenced in a formula, deduplicated, in order.
func CollectSignals(f Formula) []SignalName {
	var signals []SignalName
	seen := make(map[SignalName]bool)
	collectSignalsInto(f, &signals, seen)
	return signals
}

func collectSignalsInto(f Formula, signals *[]SignalName, seen map[SignalName]bool) {
	switch v := f.(type) {
	case Atomic:
		name := predicateSignal(v.Predicate)
		if !seen[name] {
			seen[name] = true
			*signals = append(*signals, name)
		}
	case Not:
		collectSignalsInto(v.Inner, signals, seen)
	case And:
		collectSignalsInto(v.Left, signals, seen)
		collectSignalsInto(v.Right, signals, seen)
	case Or:
		collectSignalsInto(v.Left, signals, seen)
		collectSignalsInto(v.Right, signals, seen)
	case Next:
		collectSignalsInto(v.Inner, signals, seen)
	case Always:
		collectSignalsInto(v.Inner, signals, seen)
	case Eventually:
		collectSignalsInto(v.Inner, signals, seen)
	case Until:
		collectSignalsInto(v.Left, signals, seen)
		collectSignalsInto(v.Right, signals, seen)
	case Release:
		collectSignalsInto(v.Left, signals, seen)
		collectSignalsInto(v.Right, signals, seen)
	case MetricAlways:
		collectSignalsInto(v.Inner, signals, seen)
	case MetricEventually:
		collectSignalsInto(v.Inner, signals, seen)
	case MetricUntil:
		collectSignalsInto(v.Left, signals, seen)
		collectSignalsInto(v.Right, signals, seen)
	case MetricRelease:
		collectSignalsInto(v.Left, signals, seen)
		collectSignalsInto(v.Right, signals, seen)
	}
}

// predicateSignal returns the signal name from a predicate.
func predicateSignal(p Predicate) SignalName {
	switch v := p.(type) {
	case Equals:
		return v.Signal
	case LessThan:
		return v.Signal
	case GreaterThan:
		return v.Signal
	case LessThanOrEqual:
		return v.Signal
	case GreaterThanOrEqual:
		return v.Signal
	case Between:
		return v.Signal
	case ChangedBy:
		return v.Signal
	default:
		return ""
	}
}

// formatEnrichedReason builds the enriched reason string from a diagnostic and signal values.
func formatEnrichedReason(diag PropertyDiagnostic, values map[SignalName]PhysicalValue) string {
	if len(values) == 0 {
		return "violated: " + diag.FormulaDesc
	}
	var parts []string
	for _, sig := range diag.Signals {
		if val, ok := values[sig]; ok {
			parts = append(parts, fmt.Sprintf("%s = %s", sig, formatValue(float64(val))))
		}
	}
	if len(parts) == 0 {
		return "violated: " + diag.FormulaDesc
	}
	return strings.Join(parts, ", ") + " (formula: " + diag.FormulaDesc + ")"
}

// --- Extraction cache ---

const maxExtractCache = 256

type frameKey struct {
	idValue    uint32
	isExtended bool
	data       FramePayload
}

type extractCache struct {
	entries map[frameKey]*ExtractionResult
}

func newExtractCache() *extractCache {
	return &extractCache{entries: make(map[frameKey]*ExtractionResult)}
}

func (c *extractCache) get(key frameKey) (*ExtractionResult, bool) {
	r, ok := c.entries[key]
	return r, ok
}

func (c *extractCache) put(key frameKey, result *ExtractionResult) {
	if len(c.entries) >= maxExtractCache {
		return
	}
	c.entries[key] = result
}

func (c *extractCache) clear() {
	c.entries = make(map[frameKey]*ExtractionResult)
}
