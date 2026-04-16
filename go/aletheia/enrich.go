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
// EnrichedReason is computed by the Go enrichment layer from signal values and
// formula structure; it differs from Violation.Reason and PropertyResult.Reason,
// which are raw strings from the Agda core.
type ViolationEnrichment struct {
	Signals        map[SignalName]PhysicalValue // actual values from frame (nil if extraction failed)
	FormulaDesc    string
	EnrichedReason string
	CoreReason     string // raw reason from the Agda core (e.g., "MetricEventually: window expired"); may be empty
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
	return formatFormulaInner(f, false)
}

// formatFormulaInner formats a formula. When parenthesizeBinary is true, binary
// operators (and, or, until, release) are wrapped in parentheses to avoid ambiguity.
func formatFormulaInner(f Formula, parenthesizeBinary bool) string {
	switch v := f.(type) {
	case Atomic:
		return formatPredicate(v.Predicate)
	case Not:
		return "not(" + formatFormulaInner(v.Inner, false) + ")"
	case And:
		s := formatFormulaInner(v.Left, true) + " and " + formatFormulaInner(v.Right, true)
		if parenthesizeBinary {
			return "(" + s + ")"
		}
		return s
	case Or:
		s := formatFormulaInner(v.Left, true) + " or " + formatFormulaInner(v.Right, true)
		if parenthesizeBinary {
			return "(" + s + ")"
		}
		return s
	case Next:
		return "next(" + formatFormulaInner(v.Inner, false) + ")"
	case WeakNext:
		return "weak_next(" + formatFormulaInner(v.Inner, false) + ")"
	case Always:
		// Detect Never pattern: Always{Not{Atomic{p}}}
		if n, ok := v.Inner.(Not); ok {
			if a, ok := n.Inner.(Atomic); ok {
				return "never " + formatPredicate(a.Predicate)
			}
		}
		return "always(" + formatFormulaInner(v.Inner, false) + ")"
	case Eventually:
		return "eventually(" + formatFormulaInner(v.Inner, false) + ")"
	case Until:
		s := formatFormulaInner(v.Left, true) + " until " + formatFormulaInner(v.Right, true)
		if parenthesizeBinary {
			return "(" + s + ")"
		}
		return s
	case Release:
		s := formatFormulaInner(v.Left, true) + " release " + formatFormulaInner(v.Right, true)
		if parenthesizeBinary {
			return "(" + s + ")"
		}
		return s
	case MetricAlways:
		return "always within " + formatTimebound(v.Bound) + " (" + formatFormulaInner(v.Inner, false) + ")"
	case MetricEventually:
		return "eventually within " + formatTimebound(v.Bound) + " (" + formatFormulaInner(v.Inner, false) + ")"
	case MetricUntil:
		s := formatFormulaInner(v.Left, true) + " until within " + formatTimebound(v.Bound) + " " + formatFormulaInner(v.Right, true)
		if parenthesizeBinary {
			return "(" + s + ")"
		}
		return s
	case MetricRelease:
		s := formatFormulaInner(v.Left, true) + " release within " + formatTimebound(v.Bound) + " " + formatFormulaInner(v.Right, true)
		if parenthesizeBinary {
			return "(" + s + ")"
		}
		return s
	default:
		return fmt.Sprintf("<unknown formula: %T>", f)
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
		if v.Delta >= 0 {
			return fmt.Sprintf("Δ%s >= %s", v.Signal, formatValue(float64(v.Delta)))
		}
		return fmt.Sprintf("Δ%s <= %s", v.Signal, formatValue(float64(v.Delta)))
	case StableWithin:
		return fmt.Sprintf("|Δ%s| <= %s", v.Signal, formatValue(float64(v.Tolerance)))
	default:
		return "<unknown predicate>"
	}
}

// formatValue formats a float64 without trailing zeros.
func formatValue(v float64) string { return fmt.Sprintf("%g", v) }

const (
	usPerSecond      = 1_000_000
	usPerMillisecond = 1_000
)

// formatTimebound formats a TimeBound as a human-readable time bound.
func formatTimebound(t TimeBound) string {
	us := t.Microseconds
	if us%usPerSecond == 0 {
		return fmt.Sprintf("%ds", us/usPerSecond)
	}
	if us%usPerMillisecond == 0 {
		return fmt.Sprintf("%dms", us/usPerMillisecond)
	}
	return fmt.Sprintf("%dμs", us)
}

// CollectSignals returns all signal names referenced in a formula, deduplicated, in order.
func CollectSignals(f Formula) []SignalName {
	var signals []SignalName
	seen := make(map[SignalName]bool)
	collectSignalsInto(f, &signals, seen)
	return signals
}

// collectSignalsInto appends signal names from f into *signals, skipping duplicates tracked in seen.
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
	case WeakNext:
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
	default:
		// Unknown formula types have no signals to collect. The Formula
		// interface is sealed, so this branch is unreachable for all
		// in-package types; it exists as a defensive no-op.
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
	case StableWithin:
		return v.Signal
	default:
		return ""
	}
}

// formatEnrichedReason builds the enriched reason string from a diagnostic, signal values,
// and the raw core reason. When coreReason is non-empty it is appended as context.
func formatEnrichedReason(diag PropertyDiagnostic, values map[SignalName]PhysicalValue, coreReason string) string {
	var base string
	if len(values) == 0 {
		base = "violated: " + diag.FormulaDesc
	} else {
		var parts []string
		for _, sig := range diag.Signals {
			if val, ok := values[sig]; ok {
				parts = append(parts, fmt.Sprintf("%s = %s", sig, formatValue(float64(val))))
			}
		}
		if len(parts) == 0 {
			base = "violated: " + diag.FormulaDesc
		} else {
			base = strings.Join(parts, ", ") + " (formula: " + diag.FormulaDesc + ")"
		}
	}
	if coreReason != "" {
		return base + " [core: " + coreReason + "]"
	}
	return base
}

// --- Extraction cache ---

// maxExtractCache bounds the extraction cache capacity. The cache is a plain
// bounded map (entries are rejected when the map is full — no eviction).
// 256 entries covers most production DBCs (typically 20–60 CAN IDs × 1–3
// DLC variants) with headroom for bursty traffic patterns, while keeping
// the per-Client memory footprint under ~100 KB for the map overhead.
const maxExtractCache = 256

type frameKey struct {
	idValue    uint32
	isExtended bool
	dlc        uint8
	data       string // string([]byte) for comparable map key
}

// extractCache is a bounded, frame-keyed cache of extraction results.
// It is not thread-safe; all access must be synchronized by the caller
// (protected by Client.mu).
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

// put stores a result if the cache is not full. Returns false when the cache
// is at capacity and the entry was not stored.
func (c *extractCache) put(key frameKey, result *ExtractionResult) bool {
	if len(c.entries) >= maxExtractCache {
		return false
	}
	c.entries[key] = result
	return true
}

func (c *extractCache) clear() {
	c.entries = make(map[frameKey]*ExtractionResult)
}
