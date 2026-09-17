// SPDX-FileCopyrightText: 2025 Nicolas Pelletier
// SPDX-License-Identifier: BSD-2-Clause

package aletheia

import (
	"fmt"
	"strings"
)

// formatRational is [FormatRational] for the package's own use.
func formatRational(r Rational) (string, error) {
	return formatRationalFFI(r.Numerator, r.Denominator)
}

// FormatRational renders a Rational as the display string every binding
// shares, a terminating decimal ("0.25") or a reduced fraction ("1/3"),
// through the kernel's renderer (aletheia_format_rational). The renderer
// loads the library on first use (renderer.go) and never starts the GHC
// runtime, so the call fails with an error until an FFIBackend has.
func FormatRational(r Rational) (string, error) {
	return formatRational(r)
}

// PropertyDiagnostic is what a formula yields for enriching its violations:
// the signals it names and its printed form.
type PropertyDiagnostic struct {
	Signals     []SignalName
	FormulaDesc string
}

// ViolationEnrichment is the context the binding adds to a violation: the
// signal values it extracted (nil when extraction failed), the printed
// formula, the reason it composed from them, and the core's own reason,
// which may be empty.
type ViolationEnrichment struct {
	Signals        map[SignalName]Rational
	FormulaDesc    string
	EnrichedReason string
	CoreReason     string
}

// buildDiagnostic derives a formula's diagnostic; it fails when the kernel
// renderer the printed form needs is unavailable (see [FormatRational]).
// Tests reach it through export_test.go, as the Rust build_diagnostic and
// the Python _enrichment module are reached in their bindings.
func buildDiagnostic(f Formula) (PropertyDiagnostic, error) {
	desc, err := formatFormula(f)
	if err != nil {
		return PropertyDiagnostic{}, err
	}
	return PropertyDiagnostic{
		Signals:     collectSignals(f),
		FormulaDesc: desc,
	}, nil
}

// formatFormula prints a formula; it fails as buildDiagnostic does.
func formatFormula(f Formula) (string, error) {
	p := &formulaPrinter{}
	s := p.render(f, false)
	return s, p.err
}

// formulaPrinter prints with a sticky error: once the kernel renderer has
// failed every node prints empty and formatFormula reads the one error.
type formulaPrinter struct {
	err error
}

// rat renders one threshold through the kernel.
func (p *formulaPrinter) rat(r Rational) string {
	if p.err != nil {
		return ""
	}
	s, err := formatRational(r)
	if err != nil {
		p.err = err
		return ""
	}
	return s
}

// binary prints an infix operator between its two operands, each
// parenthesised when it is binary itself, and the whole in parentheses
// when it is an operand of a binary operator.
func (p *formulaPrinter) binary(left Formula, op string, right Formula, parenthesize bool) string {
	s := p.render(left, true) + " " + op + " " + p.render(right, true)
	if parenthesize {
		return "(" + s + ")"
	}
	return s
}

// render prints a formula; parenthesizeBinary is true when the formula is an
// operand of a binary operator, so a binary formula prints in parentheses.
func (p *formulaPrinter) render(f Formula, parenthesizeBinary bool) string {
	if p.err != nil {
		return ""
	}
	switch v := f.(type) {
	case Atomic:
		return p.predicate(v.Predicate)
	case Not:
		return "not(" + p.render(v.Inner, false) + ")"
	case And:
		return p.binary(v.Left, "and", v.Right, parenthesizeBinary)
	case Or:
		return p.binary(v.Left, "or", v.Right, parenthesizeBinary)
	case Next:
		return "next(" + p.render(v.Inner, false) + ")"
	case WeakNext:
		return "weak_next(" + p.render(v.Inner, false) + ")"
	case Always:
		// always(not(p)) prints as never p
		if n, ok := v.Inner.(Not); ok {
			if a, ok := n.Inner.(Atomic); ok {
				return "never " + p.predicate(a.Predicate)
			}
		}
		return "always(" + p.render(v.Inner, false) + ")"
	case Eventually:
		return "eventually(" + p.render(v.Inner, false) + ")"
	case Until:
		return p.binary(v.Left, "until", v.Right, parenthesizeBinary)
	case Release:
		return p.binary(v.Left, "release", v.Right, parenthesizeBinary)
	case MetricAlways:
		return "always within " + formatTimebound(v.Bound) + " (" + p.render(v.Inner, false) + ")"
	case MetricEventually:
		return "eventually within " + formatTimebound(v.Bound) + " (" + p.render(v.Inner, false) + ")"
	case MetricUntil:
		return p.binary(v.Left, "until within "+formatTimebound(v.Bound), v.Right, parenthesizeBinary)
	case MetricRelease:
		return p.binary(v.Left, "release within "+formatTimebound(v.Bound), v.Right, parenthesizeBinary)
	default:
		return fmt.Sprintf("<unknown formula: %T>", f)
	}
}

// predicate prints a predicate with its thresholds rendered by the kernel.
func (p *formulaPrinter) predicate(pred Predicate) string {
	if p.err != nil {
		return ""
	}
	switch v := pred.(type) {
	case Equals:
		return fmt.Sprintf("%s = %s", v.Signal, p.rat(v.Value))
	case LessThan:
		return fmt.Sprintf("%s < %s", v.Signal, p.rat(v.Value))
	case GreaterThan:
		return fmt.Sprintf("%s > %s", v.Signal, p.rat(v.Value))
	case LessThanOrEqual:
		return fmt.Sprintf("%s <= %s", v.Signal, p.rat(v.Value))
	case GreaterThanOrEqual:
		return fmt.Sprintf("%s >= %s", v.Signal, p.rat(v.Value))
	case Between:
		return fmt.Sprintf("%s <= %s <= %s", p.rat(v.Min), v.Signal, p.rat(v.Max))
	case ChangedBy:
		if v.Delta.Numerator >= 0 {
			return fmt.Sprintf("Δ%s >= %s", v.Signal, p.rat(v.Delta))
		}
		return fmt.Sprintf("Δ%s <= %s", v.Signal, p.rat(v.Delta))
	case StableWithin:
		return fmt.Sprintf("|Δ%s| <= %s", v.Signal, p.rat(v.Tolerance))
	default:
		return "<unknown predicate>"
	}
}

const (
	usPerSecond      = 1_000_000
	usPerMillisecond = 1_000
)

// formatTimebound prints a bound in the largest unit that divides it.
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

// collectSignals is every signal a formula names, once each, in order of
// first appearance. Tests reach it through export_test.go.
func collectSignals(f Formula) []SignalName {
	var signals []SignalName
	seen := make(map[SignalName]bool)
	var walk func(Formula)
	walk = func(f Formula) {
		if a, ok := f.(Atomic); ok {
			if name := predicateSignal(a.Predicate); !seen[name] {
				seen[name] = true
				signals = append(signals, name)
			}
			return
		}
		for _, sub := range subformulas(f) {
			walk(sub)
		}
	}
	walk(f)
	return signals
}

// subformulas is the immediate operands of a formula: one for the unary
// operators, two for the binary ones, none for an atomic or for a value
// outside the sealed set (nil, a pointer to a formula, an embedding type).
func subformulas(f Formula) []Formula {
	switch v := f.(type) {
	case Not:
		return []Formula{v.Inner}
	case Next:
		return []Formula{v.Inner}
	case WeakNext:
		return []Formula{v.Inner}
	case Always:
		return []Formula{v.Inner}
	case Eventually:
		return []Formula{v.Inner}
	case MetricAlways:
		return []Formula{v.Inner}
	case MetricEventually:
		return []Formula{v.Inner}
	case And:
		return []Formula{v.Left, v.Right}
	case Or:
		return []Formula{v.Left, v.Right}
	case Until:
		return []Formula{v.Left, v.Right}
	case Release:
		return []Formula{v.Left, v.Right}
	case MetricUntil:
		return []Formula{v.Left, v.Right}
	case MetricRelease:
		return []Formula{v.Left, v.Right}
	default:
		return nil
	}
}

// predicateSignal is the signal a predicate names, empty for a value outside
// the sealed set.
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

// formatEnrichedReason is the observed values, then the core's reason when
// it has one.
func formatEnrichedReason(diag PropertyDiagnostic, values map[SignalName]Rational, coreReason string) string {
	base := formatObservedBase(diag, values)
	if coreReason != "" {
		return base + " [core: " + coreReason + "]"
	}
	return base
}

// formatObservedBase prints the observed values of the signals the
// diagnostic names, each through the kernel renderer, then the formula;
// with no value to print it falls back to the formula alone. A render
// failure falls back the same way rather than failing the frame, as the
// Python and C++ enrichment do: the frame was just processed, so the
// runtime is up and such a failure is a kernel malfunction.
func formatObservedBase(diag PropertyDiagnostic, values map[SignalName]Rational) string {
	if len(values) == 0 {
		return "violated: " + diag.FormulaDesc
	}
	var parts []string
	for _, sig := range diag.Signals {
		val, ok := values[sig]
		if !ok {
			continue
		}
		s, err := formatRational(val)
		if err != nil {
			return "violated: " + diag.FormulaDesc
		}
		parts = append(parts, fmt.Sprintf("%s = %s", sig, s))
	}
	if len(parts) == 0 {
		return "violated: " + diag.FormulaDesc
	}
	return strings.Join(parts, ", ") + " (formula: " + diag.FormulaDesc + ")"
}

// maxExtractCache bounds the extraction cache; a full cache refuses new
// entries rather than evicting. It covers a DBC of several dozen CAN IDs
// with a few DLC variants each and keeps the map overhead small.
const maxExtractCache = 256

// frameMeta is a frame's cache identity without its payload, which keys the
// inner map.
type frameMeta struct {
	idValue    uint32
	isExtended bool
	dlc        uint8
}

// extractCache is a bounded cache of extraction results keyed in two
// levels, frameMeta then payload bytes, so the hit path's map index on
// string(data) compiles without allocating (a struct key holding the
// payload would copy it on every lookup). The Client's lock serialises
// every access.
type extractCache struct {
	entries map[frameMeta]map[string]*ExtractionResult
	// count is the number of stored results across the inner maps
	count int
}

// newExtractCache is an empty cache.
func newExtractCache() *extractCache {
	return &extractCache{entries: make(map[frameMeta]map[string]*ExtractionResult)}
}

func (c *extractCache) get(meta frameMeta, data []byte) (*ExtractionResult, bool) {
	r, ok := c.entries[meta][string(data)]
	return r, ok
}

// put stores a result and reports whether it did; a full cache refuses. The
// payload is copied into an owned key only here.
func (c *extractCache) put(meta frameMeta, data []byte, result *ExtractionResult) bool {
	if c.count >= maxExtractCache {
		return false
	}
	inner, ok := c.entries[meta]
	if !ok {
		inner = make(map[string]*ExtractionResult)
		c.entries[meta] = inner
	}
	key := string(data)
	if _, exists := inner[key]; !exists {
		c.count++
	}
	inner[key] = result
	return true
}

func (c *extractCache) clear() {
	c.entries = make(map[frameMeta]map[string]*ExtractionResult)
	c.count = 0
}
