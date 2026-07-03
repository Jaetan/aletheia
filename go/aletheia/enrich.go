// SPDX-FileCopyrightText: 2025 Nicolas Pelletier
// SPDX-License-Identifier: BSD-2-Clause

package aletheia

import (
	"fmt"
	"strings"
)

// formatRational renders a Rational as a string identical across all
// bindings.  Every render flows through the Agda kernel via
// `aletheia_format_rational` (R20 cluster Y stage 2): the Go binding
// calls the same function as Python and C++, so the same Rational
// value renders to byte-identical output everywhere.
//
// The renderer dlopens the library on first use (renderer.go) but does NOT
// initialise the GHC RTS; an FFIBackend must have brought it up.  If the
// runtime is not initialised the render returns an error rather than
// self-initialising — no local Go fallback exists.
func formatRational(r Rational) (string, error) {
	return formatRationalFFI(r.Numerator, r.Denominator)
}

// FormatRational renders a Rational as the exact cross-binding display string —
// a terminating decimal ("0.25") or an exact fraction ("1/3"), never a lossy
// float — by delegating to the verified kernel renderer (the same
// aletheia_format_rational FFI used internally and by the C++/Python bindings).
// It is the public entry point for external consumers such as the cmd/aletheia
// CLI; like the internal renderer it requires a live FFIBackend and returns an
// error if the GHC RTS is not up.
func FormatRational(r Rational) (string, error) {
	return formatRational(r)
}

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
	Signals        map[SignalName]Rational // exact actual values from frame (nil if extraction failed)
	FormulaDesc    string
	EnrichedReason string
	CoreReason     string // raw reason from the Agda core (e.g., "MetricEventually: window expired"); may be empty
}

// buildDiagnostic creates a PropertyDiagnostic from a formula.  Internal:
// the public surface is the PropertyDiagnostic type (mirrors Rust
// `build_diagnostic` / Python `_enrichment`); tests reach it via
// export_test.go.
//
// Returns an error if the kernel rational renderer is unavailable — the GHC
// runtime is not initialised (create an FFIBackend first), since the formula
// description renders predicate thresholds through it.
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

// formatFormula returns a human-readable representation of an LTL formula.
// Internal — exposed to tests via export_test.go.
//
// Returns an error if the kernel rational renderer is unavailable (see
// buildDiagnostic): predicate thresholds render through it.
func formatFormula(f Formula) (string, error) {
	p := &formulaPrinter{}
	s := p.render(f, false)
	return s, p.err
}

// formulaPrinter renders a formula with a sticky error: render / predicate /
// rat short-circuit once the kernel renderer has failed, so the per-node logic
// stays free of explicit error threading and the single error is read once by
// formatFormula.
type formulaPrinter struct {
	err error
}

// rat renders one Rational via the kernel, stickying any error.
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

// render formats a formula. When parenthesizeBinary is true, binary
// operators (and, or, until, release) are wrapped in parentheses to avoid ambiguity.
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
		s := p.render(v.Left, true) + " and " + p.render(v.Right, true)
		if parenthesizeBinary {
			return "(" + s + ")"
		}
		return s
	case Or:
		s := p.render(v.Left, true) + " or " + p.render(v.Right, true)
		if parenthesizeBinary {
			return "(" + s + ")"
		}
		return s
	case Next:
		return "next(" + p.render(v.Inner, false) + ")"
	case WeakNext:
		return "weak_next(" + p.render(v.Inner, false) + ")"
	case Always:
		// Detect Never pattern: Always{Not{Atomic{p}}}
		if n, ok := v.Inner.(Not); ok {
			if a, ok := n.Inner.(Atomic); ok {
				return "never " + p.predicate(a.Predicate)
			}
		}
		return "always(" + p.render(v.Inner, false) + ")"
	case Eventually:
		return "eventually(" + p.render(v.Inner, false) + ")"
	case Until:
		s := p.render(v.Left, true) + " until " + p.render(v.Right, true)
		if parenthesizeBinary {
			return "(" + s + ")"
		}
		return s
	case Release:
		s := p.render(v.Left, true) + " release " + p.render(v.Right, true)
		if parenthesizeBinary {
			return "(" + s + ")"
		}
		return s
	case MetricAlways:
		return "always within " + formatTimebound(v.Bound) + " (" + p.render(v.Inner, false) + ")"
	case MetricEventually:
		return "eventually within " + formatTimebound(v.Bound) + " (" + p.render(v.Inner, false) + ")"
	case MetricUntil:
		s := p.render(v.Left, true) + " until within " + formatTimebound(v.Bound) + " " + p.render(v.Right, true)
		if parenthesizeBinary {
			return "(" + s + ")"
		}
		return s
	case MetricRelease:
		s := p.render(v.Left, true) + " release within " + formatTimebound(v.Bound) + " " + p.render(v.Right, true)
		if parenthesizeBinary {
			return "(" + s + ")"
		}
		return s
	default:
		return fmt.Sprintf("<unknown formula: %T>", f)
	}
}

// predicate renders a predicate, stickying any kernel-renderer error.
// Display path only — Rational values flow through the kernel (formatRational),
// which renders terminating fractions as decimals and non-terminating ones as
// reduced N/D (e.g. Rational{1, 3} → "1/3").
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

// collectSignals returns all signal names referenced in a formula, deduplicated, in order.
// Internal (mirrors the peers); exposed to tests via export_test.go.
func collectSignals(f Formula) []SignalName {
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
		// Formula is sealed (the unexported formula() marker method), so
		// the concrete formula types above are exhaustive; this arm is
		// reached only by degenerate values (nil, a *T pointer to a
		// concrete formula type, or an embedding type), which are treated
		// as contributing no signals.
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
		// Predicate is sealed (the unexported predicate() marker method),
		// so the concrete predicate types above are exhaustive; degenerate
		// values (nil, a pointer, or an embedding type) fall through here.
		// The return also satisfies Go's missing-return rule.
		return ""
	}
}

// formatEnrichedReason builds the enriched reason string from a diagnostic, signal values,
// and the raw core reason. When coreReason is non-empty it is appended as context.
func formatEnrichedReason(diag PropertyDiagnostic, values map[SignalName]Rational, coreReason string) string {
	base := formatObservedBase(diag, values)
	if coreReason != "" {
		return base + " [core: " + coreReason + "]"
	}
	return base
}

// formatObservedBase renders the observed-values portion of an enriched reason.
// Each observed value renders via the kernel formatℚ (formatRational) — exact,
// not lossy %g, and byte-identical to the other bindings.
//
// Eval-path degrade (parity with Python format_enriched_reason and C++
// client.cpp): this renders an ALREADY-PROCESSED frame's observed values, so the
// GHC runtime is necessarily up (a frame was just processed) and a render
// failure can only be a catastrophic null kernel return — degrade the whole
// reason to the formula description rather than propagating, so an enriched
// reason never sinks a processed frame.
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

// --- Extraction cache ---

// maxExtractCache bounds the extraction cache capacity. The cache is a plain
// bounded map (entries are rejected when the map is full — no eviction).
// 256 entries covers most production DBCs (typically 20–60 CAN IDs × 1–3
// DLC variants) with headroom for bursty traffic patterns, while keeping
// the per-Client memory footprint under ~100 KB for the map overhead.
const maxExtractCache = 256

// frameMeta is the payload-free part of a frame's cache identity; the
// payload bytes form the inner map key (see extractCache.entries).
type frameMeta struct {
	idValue    uint32
	isExtended bool
	dlc        uint8
}

// extractCache is a bounded, frame-keyed cache of extraction results.
// Keyed in two levels — frameMeta, then payload bytes — so the hit-path
// lookup `entries[meta][string(data)]` compiles to Go's allocation-free
// []byte→string map-index form. (A flat struct key with a string field
// forces a heap copy of the payload on every lookup, including hits,
// because the key value also flows into put on the miss branch.)
// It is not thread-safe; all access must be synchronized by the caller
// (the Client's channel-token lock, lockCh).
type extractCache struct {
	entries map[frameMeta]map[string]*ExtractionResult
	// count is the total number of stored results across the inner maps,
	// keeping the maxExtractCache bound exact without a per-put sum.
	count int
}

// newExtractCache returns an empty extract cache. Use it once per
// Client; the cache is not safe for concurrent use and the Client holds
// its channel-token lock (lockCh) whenever it reads or writes entries.
func newExtractCache() *extractCache {
	return &extractCache{entries: make(map[frameMeta]map[string]*ExtractionResult)}
}

func (c *extractCache) get(meta frameMeta, data []byte) (*ExtractionResult, bool) {
	r, ok := c.entries[meta][string(data)]
	return r, ok
}

// put stores a result if the cache is not full. Returns false when the cache
// is at capacity and the entry was not stored. The payload is materialized
// as an owned string key only here, on the store path.
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
