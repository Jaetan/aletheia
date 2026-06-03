// SPDX-FileCopyrightText: 2025 Nicolas Pelletier
// SPDX-License-Identifier: BSD-2-Clause

package aletheia_test

import (
	"strings"
	"sync"
	"testing"

	"github.com/aletheia-automotive/aletheia-go/aletheia"
)

// --- Formula pretty-printing ---

func TestFormatFormula_AlwaysLessThan(t *testing.T) {
	f := aletheia.Always{Inner: aletheia.Atomic{Predicate: aletheia.LessThan{Signal: "Speed", Value: aletheia.RationalFromFloat(220)}}}
	got := aletheia.FormatFormula(f)
	expected := "always(Speed < 220)"
	if got != expected {
		t.Errorf("got %q, want %q", got, expected)
	}
}

func TestFormatFormula_NeverPattern(t *testing.T) {
	f := aletheia.Never(aletheia.GreaterThan{Signal: "Speed", Value: aletheia.RationalFromFloat(100)})
	got := aletheia.FormatFormula(f)
	expected := "never Speed > 100"
	if got != expected {
		t.Errorf("got %q, want %q", got, expected)
	}
}

func TestFormatFormula_Eventually(t *testing.T) {
	f := aletheia.Eventually{Inner: aletheia.Atomic{Predicate: aletheia.Equals{Signal: "Mode", Value: aletheia.RationalFromFloat(1)}}}
	got := aletheia.FormatFormula(f)
	expected := "eventually(Mode = 1)"
	if got != expected {
		t.Errorf("got %q, want %q", got, expected)
	}
}

func TestFormatFormula_MetricAlways(t *testing.T) {
	f := aletheia.MetricAlways{
		Bound: aletheia.TimeBound{Microseconds: 5000000},
		Inner: aletheia.Atomic{Predicate: aletheia.LessThan{Signal: "Speed", Value: aletheia.RationalFromFloat(220)}},
	}
	got := aletheia.FormatFormula(f)
	expected := "always within 5s (Speed < 220)"
	if got != expected {
		t.Errorf("got %q, want %q", got, expected)
	}
}

func TestFormatFormula_MetricEventually(t *testing.T) {
	f := aletheia.MetricEventually{
		Bound: aletheia.TimeBound{Microseconds: 2000000},
		Inner: aletheia.Atomic{Predicate: aletheia.Equals{Signal: "Mode", Value: aletheia.RationalFromFloat(1)}},
	}
	got := aletheia.FormatFormula(f)
	expected := "eventually within 2s (Mode = 1)"
	if got != expected {
		t.Errorf("got %q, want %q", got, expected)
	}
}

func TestFormatFormula_Next(t *testing.T) {
	f := aletheia.Next{Inner: aletheia.Atomic{Predicate: aletheia.LessThan{Signal: "Speed", Value: aletheia.RationalFromFloat(220)}}}
	got := aletheia.FormatFormula(f)
	expected := "next(Speed < 220)"
	if got != expected {
		t.Errorf("got %q, want %q", got, expected)
	}
}

func TestFormatFormula_And(t *testing.T) {
	f := aletheia.And{
		Left:  aletheia.Atomic{Predicate: aletheia.LessThan{Signal: "Speed", Value: aletheia.RationalFromFloat(220)}},
		Right: aletheia.Atomic{Predicate: aletheia.GreaterThan{Signal: "RPM", Value: aletheia.RationalFromFloat(500)}},
	}
	got := aletheia.FormatFormula(f)
	expected := "Speed < 220 and RPM > 500"
	if got != expected {
		t.Errorf("got %q, want %q", got, expected)
	}
}

func TestFormatFormula_Complex(t *testing.T) {
	// always(Speed < 220 and RPM > 500)
	f := aletheia.Always{Inner: aletheia.And{
		Left:  aletheia.Atomic{Predicate: aletheia.LessThan{Signal: "Speed", Value: aletheia.RationalFromFloat(220)}},
		Right: aletheia.Atomic{Predicate: aletheia.GreaterThan{Signal: "RPM", Value: aletheia.RationalFromFloat(500)}},
	}}
	got := aletheia.FormatFormula(f)
	expected := "always(Speed < 220 and RPM > 500)"
	if got != expected {
		t.Errorf("got %q, want %q", got, expected)
	}
}

func TestFormatFormula_Until(t *testing.T) {
	f := aletheia.Until{
		Left:  aletheia.Atomic{Predicate: aletheia.GreaterThan{Signal: "RPM", Value: aletheia.RationalFromFloat(500)}},
		Right: aletheia.Atomic{Predicate: aletheia.LessThan{Signal: "Speed", Value: aletheia.RationalFromFloat(220)}},
	}
	got := aletheia.FormatFormula(f)
	expected := "RPM > 500 until Speed < 220"
	if got != expected {
		t.Errorf("got %q, want %q", got, expected)
	}
}

func TestFormatFormula_AllPredicates(t *testing.T) {
	tests := []struct {
		pred     aletheia.Predicate
		expected string
	}{
		{aletheia.Equals{Signal: "S", Value: aletheia.RationalFromFloat(10)}, "S = 10"},
		{aletheia.LessThan{Signal: "S", Value: aletheia.RationalFromFloat(10)}, "S < 10"},
		{aletheia.GreaterThan{Signal: "S", Value: aletheia.RationalFromFloat(10)}, "S > 10"},
		{aletheia.LessThanOrEqual{Signal: "S", Value: aletheia.RationalFromFloat(10)}, "S <= 10"},
		{aletheia.GreaterThanOrEqual{Signal: "S", Value: aletheia.RationalFromFloat(10)}, "S >= 10"},
		{aletheia.Between{Signal: "S", Min: aletheia.RationalFromFloat(5), Max: aletheia.RationalFromFloat(15)}, "5 <= S <= 15"},
		{aletheia.ChangedBy{Signal: "S", Delta: aletheia.RationalFromFloat(2.5)}, "ΔS >= 2.5"},
		{aletheia.ChangedBy{Signal: "S", Delta: aletheia.RationalFromFloat(-3)}, "ΔS <= -3"},
		{aletheia.StableWithin{Signal: "S", Tolerance: aletheia.RationalFromFloat(2.5)}, "|ΔS| <= 2.5"},
	}
	for _, tt := range tests {
		f := aletheia.Atomic{Predicate: tt.pred}
		got := aletheia.FormatFormula(f)
		if got != tt.expected {
			t.Errorf("pred %T: got %q, want %q", tt.pred, got, tt.expected)
		}
	}
}

func TestFormatFormula_NonTerminatingRational(t *testing.T) {
	tests := []struct {
		name     string
		pred     aletheia.Predicate
		expected string
	}{
		{"equals 1/3", aletheia.Equals{Signal: "S", Value: aletheia.Rational{Numerator: 1, Denominator: 3}}, "S = 1/3"},
		{"less_than 2/7", aletheia.LessThan{Signal: "S", Value: aletheia.Rational{Numerator: 2, Denominator: 7}}, "S < 2/7"},
		{"greater_than -1/3", aletheia.GreaterThan{Signal: "S", Value: aletheia.Rational{Numerator: -1, Denominator: 3}}, "S > -1/3"},
		{"between non-terminating", aletheia.Between{Signal: "S", Min: aletheia.Rational{Numerator: 1, Denominator: 3}, Max: aletheia.Rational{Numerator: 2, Denominator: 3}}, "1/3 <= S <= 2/3"},
		{"reduces 2/6 → 1/3", aletheia.Equals{Signal: "S", Value: aletheia.Rational{Numerator: 2, Denominator: 6}}, "S = 1/3"},
		{"changed_by 1/3", aletheia.ChangedBy{Signal: "S", Delta: aletheia.Rational{Numerator: 1, Denominator: 3}}, "ΔS >= 1/3"},
		{"stable_within 1/7", aletheia.StableWithin{Signal: "S", Tolerance: aletheia.Rational{Numerator: 1, Denominator: 7}}, "|ΔS| <= 1/7"},
		// k > 18 cases: terminating in decimal but the multiplier would
		// overflow int64; render as N/D for cross-binding byte-identity
		// with Python and C++ (which apply the same fallback).
		{"k=19 power-of-2 → 1/524288", aletheia.Equals{Signal: "S", Value: aletheia.Rational{Numerator: 1, Denominator: 524288}}, "S = 1/524288"},
		{"k=19 power-of-5 → 1/19073486328125", aletheia.Equals{Signal: "S", Value: aletheia.Rational{Numerator: 1, Denominator: 19073486328125}}, "S = 1/19073486328125"},
		{"k=25 → -1/33554432 (negative, large k)", aletheia.Equals{Signal: "S", Value: aletheia.Rational{Numerator: -1, Denominator: 33554432}}, "S = -1/33554432"},
	}
	for _, tt := range tests {
		f := aletheia.Atomic{Predicate: tt.pred}
		got := aletheia.FormatFormula(f)
		if got != tt.expected {
			t.Errorf("%s: got %q, want %q", tt.name, got, tt.expected)
		}
	}
}

func TestFormatFormula_TerminatingRationalExact(t *testing.T) {
	// Direct-construction Rational with terminating reduced denom renders as
	// exact decimal in all three bindings (Go, C++, Python) — no precision
	// loss to %g / :g defaults.  Includes large integers and high-precision
	// decimals that previously diverged across bindings under the :g/%g path.
	tests := []struct {
		name     string
		pred     aletheia.Predicate
		expected string
	}{
		{"23/2 → 11.5", aletheia.LessThan{Signal: "V", Value: aletheia.Rational{Numerator: 23, Denominator: 2}}, "V < 11.5"},
		{"7/8 → 0.875", aletheia.Equals{Signal: "S", Value: aletheia.Rational{Numerator: 7, Denominator: 8}}, "S = 0.875"},
		{"42/1 → 42", aletheia.Equals{Signal: "S", Value: aletheia.Rational{Numerator: 42, Denominator: 1}}, "S = 42"},
		{"-23/2 → -11.5", aletheia.Equals{Signal: "S", Value: aletheia.Rational{Numerator: -23, Denominator: 2}}, "S = -11.5"},
		{"1234567/1 → 1234567 (no scientific)", aletheia.Equals{Signal: "S", Value: aletheia.Rational{Numerator: 1234567, Denominator: 1}}, "S = 1234567"},
		{"123456789/10^9 → 0.123456789 (9 sig figs exact)", aletheia.Equals{Signal: "S", Value: aletheia.Rational{Numerator: 123456789, Denominator: 1000000000}}, "S = 0.123456789"},
		{"1/1000000 → 0.000001 (small, no scientific)", aletheia.Equals{Signal: "S", Value: aletheia.Rational{Numerator: 1, Denominator: 1000000}}, "S = 0.000001"},
		{"50/100 → 0.5 (reduces, trims trailing zero)", aletheia.Equals{Signal: "S", Value: aletheia.Rational{Numerator: 50, Denominator: 100}}, "S = 0.5"},
		{"0/5 → 0 (zero)", aletheia.Equals{Signal: "S", Value: aletheia.Rational{Numerator: 0, Denominator: 5}}, "S = 0"},
		{"1/262144 → 0.000003814697265625 (k=18 boundary, last decimal)", aletheia.Equals{Signal: "S", Value: aletheia.Rational{Numerator: 1, Denominator: 262144}}, "S = 0.000003814697265625"},
	}
	for _, tt := range tests {
		f := aletheia.Atomic{Predicate: tt.pred}
		got := aletheia.FormatFormula(f)
		if got != tt.expected {
			t.Errorf("%s: got %q, want %q", tt.name, got, tt.expected)
		}
	}
}

func TestFormatFormula_Release(t *testing.T) {
	f := aletheia.Release{
		Left:  aletheia.Atomic{Predicate: aletheia.GreaterThan{Signal: "RPM", Value: aletheia.RationalFromFloat(500)}},
		Right: aletheia.Atomic{Predicate: aletheia.LessThan{Signal: "Speed", Value: aletheia.RationalFromFloat(220)}},
	}
	got := aletheia.FormatFormula(f)
	expected := "RPM > 500 release Speed < 220"
	if got != expected {
		t.Errorf("got %q, want %q", got, expected)
	}
}

func TestFormatFormula_NestedBinaryParens(t *testing.T) {
	// And{Or{a, b}, c} should produce "(a or b) and c", not "a or b and c"
	a := aletheia.Atomic{Predicate: aletheia.LessThan{Signal: "Speed", Value: aletheia.RationalFromFloat(220)}}
	b := aletheia.Atomic{Predicate: aletheia.GreaterThan{Signal: "RPM", Value: aletheia.RationalFromFloat(500)}}
	c := aletheia.Atomic{Predicate: aletheia.LessThan{Signal: "Temp", Value: aletheia.RationalFromFloat(80)}}
	f := aletheia.And{
		Left:  aletheia.Or{Left: a, Right: b},
		Right: c,
	}
	got := aletheia.FormatFormula(f)
	expected := "(Speed < 220 or RPM > 500) and Temp < 80"
	if got != expected {
		t.Errorf("got %q, want %q", got, expected)
	}
}

// --- Signal collection ---

func TestCollectSignals_MultiSignal(t *testing.T) {
	f := aletheia.And{
		Left:  aletheia.Atomic{Predicate: aletheia.LessThan{Signal: "Speed", Value: aletheia.RationalFromFloat(220)}},
		Right: aletheia.Atomic{Predicate: aletheia.GreaterThan{Signal: "RPM", Value: aletheia.RationalFromFloat(500)}},
	}
	signals := aletheia.CollectSignals(f)
	if len(signals) != 2 {
		t.Fatalf("expected 2 signals, got %d", len(signals))
	}
	if signals[0] != "Speed" || signals[1] != "RPM" {
		t.Errorf("got %v, want [Speed, RPM]", signals)
	}
}

func TestCollectSignals_Dedup(t *testing.T) {
	f := aletheia.And{
		Left:  aletheia.Atomic{Predicate: aletheia.LessThan{Signal: "Speed", Value: aletheia.RationalFromFloat(220)}},
		Right: aletheia.Atomic{Predicate: aletheia.GreaterThan{Signal: "Speed", Value: aletheia.RationalFromFloat(0)}},
	}
	signals := aletheia.CollectSignals(f)
	if len(signals) != 1 {
		t.Fatalf("expected 1 signal (deduped), got %d: %v", len(signals), signals)
	}
	if signals[0] != "Speed" {
		t.Errorf("got %v, want [Speed]", signals)
	}
}

func TestBuildDiagnostic_AlwaysSucceeds(t *testing.T) {
	formulas := []aletheia.Formula{
		aletheia.Atomic{Predicate: aletheia.LessThan{Signal: "S", Value: aletheia.RationalFromFloat(1)}},
		aletheia.Not{Inner: aletheia.Atomic{Predicate: aletheia.Equals{Signal: "S", Value: aletheia.RationalFromFloat(1)}}},
		aletheia.And{
			Left:  aletheia.Atomic{Predicate: aletheia.LessThan{Signal: "A", Value: aletheia.RationalFromFloat(1)}},
			Right: aletheia.Atomic{Predicate: aletheia.GreaterThan{Signal: "B", Value: aletheia.RationalFromFloat(2)}},
		},
		aletheia.Or{
			Left:  aletheia.Atomic{Predicate: aletheia.LessThan{Signal: "A", Value: aletheia.RationalFromFloat(1)}},
			Right: aletheia.Atomic{Predicate: aletheia.GreaterThan{Signal: "B", Value: aletheia.RationalFromFloat(2)}},
		},
		aletheia.Always{Inner: aletheia.Atomic{Predicate: aletheia.LessThan{Signal: "S", Value: aletheia.RationalFromFloat(1)}}},
		aletheia.Eventually{Inner: aletheia.Atomic{Predicate: aletheia.LessThan{Signal: "S", Value: aletheia.RationalFromFloat(1)}}},
		aletheia.Next{Inner: aletheia.Atomic{Predicate: aletheia.LessThan{Signal: "S", Value: aletheia.RationalFromFloat(1)}}},
		aletheia.Until{
			Left:  aletheia.Atomic{Predicate: aletheia.LessThan{Signal: "A", Value: aletheia.RationalFromFloat(1)}},
			Right: aletheia.Atomic{Predicate: aletheia.GreaterThan{Signal: "B", Value: aletheia.RationalFromFloat(2)}},
		},
		aletheia.Release{
			Left:  aletheia.Atomic{Predicate: aletheia.LessThan{Signal: "A", Value: aletheia.RationalFromFloat(1)}},
			Right: aletheia.Atomic{Predicate: aletheia.GreaterThan{Signal: "B", Value: aletheia.RationalFromFloat(2)}},
		},
		aletheia.MetricAlways{Bound: aletheia.TimeBound{Microseconds: 1000000}, Inner: aletheia.Atomic{Predicate: aletheia.LessThan{Signal: "S", Value: aletheia.RationalFromFloat(1)}}},
		aletheia.MetricEventually{Bound: aletheia.TimeBound{Microseconds: 1000000}, Inner: aletheia.Atomic{Predicate: aletheia.LessThan{Signal: "S", Value: aletheia.RationalFromFloat(1)}}},
		aletheia.MetricUntil{Bound: aletheia.TimeBound{Microseconds: 1000000}, Left: aletheia.Atomic{Predicate: aletheia.LessThan{Signal: "A", Value: aletheia.RationalFromFloat(1)}}, Right: aletheia.Atomic{Predicate: aletheia.GreaterThan{Signal: "B", Value: aletheia.RationalFromFloat(2)}}},
		aletheia.MetricRelease{Bound: aletheia.TimeBound{Microseconds: 1000000}, Left: aletheia.Atomic{Predicate: aletheia.LessThan{Signal: "A", Value: aletheia.RationalFromFloat(1)}}, Right: aletheia.Atomic{Predicate: aletheia.GreaterThan{Signal: "B", Value: aletheia.RationalFromFloat(2)}}},
	}
	for i, f := range formulas {
		diag := aletheia.BuildDiagnostic(f)
		if diag.FormulaDesc == "" {
			t.Errorf("formula %d: empty FormulaDesc", i)
		}
		if len(diag.Signals) == 0 {
			t.Errorf("formula %d: empty Signals", i)
		}
	}
}

// --- Enrichment integration ---

func TestSetProperties_AutoDerive(t *testing.T) {
	mock := aletheia.NewMockBackend(
		aletheia.Respond(`{"status":"success"}`), // SetProperties
	)
	c, err := aletheia.NewClient(mock)
	if err != nil {
		t.Fatal(err)
	}
	defer c.Close()

	err = c.SetProperties(ctx, []aletheia.Formula{
		aletheia.Always{Inner: aletheia.Atomic{Predicate: aletheia.LessThan{Signal: "Speed", Value: aletheia.RationalFromFloat(220)}}},
	})
	if err != nil {
		t.Fatalf("SetProperties: %v", err)
	}
	// Diagnostics are internal; we verify by triggering enrichment below.
}

func TestSendFrame_EnrichedViolation(t *testing.T) {
	mock := aletheia.NewMockBackend(
		aletheia.Respond(`{"status":"success"}`), // SetProperties
		aletheia.Respond(`{"status":"success"}`), // StartStream
		// SendFrame violation response (consumed first by processLocked)
		aletheia.Respond(`{"type":"property_batch","results":[{"type":"property","status":"fails","property_index":0,"timestamp":2000000,"reason":"Atomic: predicate failed"}]}`),
		// Extraction response (consumed by enrichment's extractSignalsLocked)
		aletheia.Respond(`{"status":"success","values":[{"name":"Speed","value":245}],"errors":[],"absent":[]}`),
	)
	c, err := aletheia.NewClient(mock)
	if err != nil {
		t.Fatal(err)
	}
	defer c.Close()

	err = c.SetProperties(ctx, []aletheia.Formula{
		aletheia.Always{Inner: aletheia.Atomic{Predicate: aletheia.LessThan{Signal: "Speed", Value: aletheia.RationalFromFloat(220)}}},
	})
	if err != nil {
		t.Fatalf("SetProperties: %v", err)
	}
	err = c.StartStream(ctx)
	if err != nil {
		t.Fatalf("StartStream: %v", err)
	}

	sid, _ := aletheia.NewStandardID(0x123)
	data := aletheia.FramePayload{0xF5, 0x09, 0, 0, 0, 0, 0, 0}
	resp, err := c.SendFrame(ctx, aletheia.Timestamp{Microseconds: 2000000}, sid, dlc8(), data, nil, nil)
	if err != nil {
		t.Fatalf("SendFrame: %v", err)
	}

	b, ok := resp.(aletheia.PropertyBatch)

	if !ok {
		t.Fatalf("expected PropertyBatch, got %T", resp)

	}

	v := b.FirstViolation()

	if v == nil {
		t.Fatalf("expected violation in batch, got %+v", b)

	}
	if v.Enrichment == nil {
		t.Fatal("expected non-nil Enrichment")
	}
	if v.Enrichment.FormulaDesc != "always(Speed < 220)" {
		t.Errorf("FormulaDesc = %q", v.Enrichment.FormulaDesc)
	}
	if val, ok := v.Enrichment.Signals["Speed"]; !ok || val != 245 {
		t.Errorf("Signals = %v, want Speed=245", v.Enrichment.Signals)
	}
	if !strings.Contains(v.Enrichment.EnrichedReason, "Speed = 245") {
		t.Errorf("EnrichedReason = %q, want to contain 'Speed = 245'", v.Enrichment.EnrichedReason)
	}
	if !strings.Contains(v.Enrichment.EnrichedReason, "always(Speed < 220)") {
		t.Errorf("EnrichedReason = %q, want to contain formula", v.Enrichment.EnrichedReason)
	}
}

func TestSendFrame_MultiSignalEnrichment(t *testing.T) {
	mock := aletheia.NewMockBackend(
		aletheia.Respond(`{"status":"success"}`), // SetProperties
		aletheia.Respond(`{"status":"success"}`), // StartStream
		// Violation response (consumed first by processLocked)
		aletheia.Respond(`{"type":"property_batch","results":[{"type":"property","status":"fails","property_index":0,"timestamp":2000000,"reason":"Atomic: predicate failed"}]}`),
		// Extraction response (consumed by enrichment)
		aletheia.Respond(`{"status":"success","values":[{"name":"Speed","value":245},{"name":"RPM","value":3000}],"errors":[],"absent":[]}`),
	)
	c, err := aletheia.NewClient(mock)
	if err != nil {
		t.Fatal(err)
	}
	defer c.Close()

	err = c.SetProperties(ctx, []aletheia.Formula{
		aletheia.Always{Inner: aletheia.And{
			Left:  aletheia.Atomic{Predicate: aletheia.LessThan{Signal: "Speed", Value: aletheia.RationalFromFloat(220)}},
			Right: aletheia.Atomic{Predicate: aletheia.GreaterThan{Signal: "RPM", Value: aletheia.RationalFromFloat(500)}},
		}},
	})
	if err != nil {
		t.Fatalf("SetProperties: %v", err)
	}
	err = c.StartStream(ctx)
	if err != nil {
		t.Fatalf("StartStream: %v", err)
	}

	sid, _ := aletheia.NewStandardID(0x123)
	data := aletheia.FramePayload{0xF5, 0x09, 0, 0, 0, 0, 0, 0}
	resp, err := c.SendFrame(ctx, aletheia.Timestamp{Microseconds: 2000000}, sid, dlc8(), data, nil, nil)
	if err != nil {
		t.Fatalf("SendFrame: %v", err)
	}

	b, ok := resp.(aletheia.PropertyBatch)

	if !ok {
		t.Fatalf("expected PropertyBatch, got %T", resp)

	}

	v := b.FirstViolation()

	if v == nil {
		t.Fatalf("expected violation in batch, got %+v", b)

	}
	if v.Enrichment == nil {
		t.Fatal("expected non-nil Enrichment")
	}
	if len(v.Enrichment.Signals) != 2 {
		t.Errorf("expected 2 signals, got %d: %v", len(v.Enrichment.Signals), v.Enrichment.Signals)
	}
	if !strings.Contains(v.Enrichment.EnrichedReason, "Speed = 245") {
		t.Errorf("EnrichedReason = %q, want Speed=245", v.Enrichment.EnrichedReason)
	}
	if !strings.Contains(v.Enrichment.EnrichedReason, "RPM = 3000") {
		t.Errorf("EnrichedReason = %q, want RPM=3000", v.Enrichment.EnrichedReason)
	}
}

func TestSendFrame_ExtractionCaching(t *testing.T) {
	mock := aletheia.NewMockBackend(
		aletheia.Respond(`{"status":"success"}`), // SetProperties
		aletheia.Respond(`{"status":"success"}`), // StartStream
		// First violation, then extraction (cached)
		aletheia.Respond(`{"type":"property_batch","results":[{"type":"property","status":"fails","property_index":0,"timestamp":1000000,"reason":"test"}]}`),
		aletheia.Respond(`{"status":"success","values":[{"name":"Speed","value":245}],"errors":[],"absent":[]}`),
		// Second violation with same frame — no new extraction (cache hit)
		aletheia.Respond(`{"type":"property_batch","results":[{"type":"property","status":"fails","property_index":0,"timestamp":2000000,"reason":"test"}]}`),
	)
	c, err := aletheia.NewClient(mock)
	if err != nil {
		t.Fatal(err)
	}
	defer c.Close()

	err = c.SetProperties(ctx, []aletheia.Formula{
		aletheia.Always{Inner: aletheia.Atomic{Predicate: aletheia.LessThan{Signal: "Speed", Value: aletheia.RationalFromFloat(220)}}},
	})
	if err != nil {
		t.Fatal(err)
	}
	err = c.StartStream(ctx)
	if err != nil {
		t.Fatal(err)
	}

	sid, _ := aletheia.NewStandardID(0x123)
	data := aletheia.FramePayload{0xF5, 0x09, 0, 0, 0, 0, 0, 0}

	resp1, err := c.SendFrame(ctx, aletheia.Timestamp{Microseconds: 1000000}, sid, dlc8(), data, nil, nil)
	if err != nil {
		t.Fatal(err)
	}
	b1, ok := resp1.(aletheia.PropertyBatch)
	if !ok {
		t.Fatalf("expected PropertyBatch, got %T", resp1)
	}
	v1 := b1.FirstViolation()
	if v1 == nil || v1.Enrichment == nil {
		t.Fatal("expected enriched violation 1")
	}

	resp2, err := c.SendFrame(ctx, aletheia.Timestamp{Microseconds: 2000000}, sid, dlc8(), data, nil, nil)
	if err != nil {
		t.Fatal(err)
	}
	b2, ok := resp2.(aletheia.PropertyBatch)
	if !ok {
		t.Fatalf("expected PropertyBatch, got %T", resp2)
	}
	v2 := b2.FirstViolation()
	if v2 == nil || v2.Enrichment == nil {
		t.Fatal("expected enriched violation 2")
	}

	// Both should have the same value — only 1 extraction call was made.
	if v2.Enrichment.Signals["Speed"] != 245 {
		t.Errorf("expected cached Speed=245, got %v", v2.Enrichment.Signals["Speed"])
	}

	// Mock had 5 responses: SetProperties, StartStream, Extraction, Violation1, Violation2.
	// If extraction was called twice, mock would have run out.
	if got := len(mock.Inputs()); got != 5 {
		t.Errorf("expected 5 mock calls (1 extraction), got %d", got)
	}
}

func TestSendFrame_CacheBounded(t *testing.T) {
	// Build mock responses for 257 violations with unique frames, each needing extraction.
	var responses []aletheia.MockResponse
	responses = append(responses, aletheia.Respond(`{"status":"success"}`)) // SetProperties
	responses = append(responses, aletheia.Respond(`{"status":"success"}`)) // StartStream

	// First 256 frames: violation then extraction (cached)
	for i := 0; i < 256; i++ {
		responses = append(responses, aletheia.Respond(`{"type":"property_batch","results":[{"type":"property","status":"fails","property_index":0,"timestamp":1000,"reason":"test"}]}`))
		responses = append(responses, aletheia.Respond(`{"status":"success","values":[{"name":"Speed","value":100}],"errors":[],"absent":[]}`))
	}
	// 257th frame: violation, then extraction (extracted but not cached — cache full)
	responses = append(responses, aletheia.Respond(`{"type":"property_batch","results":[{"type":"property","status":"fails","property_index":0,"timestamp":1000,"reason":"test"}]}`))
	responses = append(responses, aletheia.Respond(`{"status":"success","values":[{"name":"Speed","value":100}],"errors":[],"absent":[]}`))

	mock := aletheia.NewMockBackend(responses...)
	c, err := aletheia.NewClient(mock)
	if err != nil {
		t.Fatal(err)
	}
	defer c.Close()

	err = c.SetProperties(ctx, []aletheia.Formula{
		aletheia.Always{Inner: aletheia.Atomic{Predicate: aletheia.LessThan{Signal: "Speed", Value: aletheia.RationalFromFloat(220)}}},
	})
	if err != nil {
		t.Fatal(err)
	}
	err = c.StartStream(ctx)
	if err != nil {
		t.Fatal(err)
	}

	for i := 0; i < 257; i++ {
		sid, _ := aletheia.NewStandardID(uint16(i % 2048))
		data := aletheia.FramePayload{byte(i), byte(i >> 8), 0, 0, 0, 0, 0, 0}
		resp, err := c.SendFrame(ctx, aletheia.Timestamp{Microseconds: 1000}, sid, dlc8(), data, nil, nil)
		if err != nil {
			t.Fatalf("SendFrame %d: %v", i, err)
		}
		b, ok := resp.(aletheia.PropertyBatch)

		if !ok {
			t.Fatalf("expected PropertyBatch, got %T", resp)

		}

		v := b.FirstViolation()

		if v == nil {
			t.Fatalf("expected violation in batch, got %+v", b)

		}
		// All frames enriched (extraction happens regardless, just not cached after 256)
		if v.Enrichment == nil {
			t.Errorf("frame %d: expected enrichment", i)
		}
	}
}

func TestEndStream_Enriched(t *testing.T) {
	mock := aletheia.NewMockBackend(
		aletheia.Respond(`{"status":"success"}`), // SetProperties
		aletheia.Respond(`{"status":"success"}`), // StartStream
		aletheia.Respond(`{"status":"ack"}`),     // SendFrame
		aletheia.Respond(`{
			"status":"complete",
			"results":[{"property_index":0,"status":"fails","timestamp":5000000,"reason":"Atomic: predicate failed"}]
		}`), // EndStream
		aletheia.Respond(`{"status":"success","values":[{"name":"Speed","value":150}],"errors":[],"absent":[]}`), // EOS extraction
	)
	c, err := aletheia.NewClient(mock)
	if err != nil {
		t.Fatal(err)
	}
	defer c.Close()

	err = c.SetProperties(ctx, []aletheia.Formula{
		aletheia.Always{Inner: aletheia.Atomic{Predicate: aletheia.LessThan{Signal: "Speed", Value: aletheia.RationalFromFloat(220)}}},
	})
	if err != nil {
		t.Fatal(err)
	}
	err = c.StartStream(ctx)
	if err != nil {
		t.Fatal(err)
	}

	sid, _ := aletheia.NewStandardID(0x123)
	data := aletheia.FramePayload{0, 0, 0, 0, 0, 0, 0, 0}
	_, err = c.SendFrame(ctx, aletheia.Timestamp{Microseconds: 1000}, sid, dlc8(), data, nil, nil)
	if err != nil {
		t.Fatal(err)
	}

	sr, err := c.EndStream(ctx)
	if err != nil {
		t.Fatalf("EndStream: %v", err)
	}
	if len(sr.Results) != 1 {
		t.Fatalf("expected 1 result, got %d", len(sr.Results))
	}
	pr := sr.Results[0]
	if pr.Verdict != aletheia.Fails {
		t.Fatalf("expected Fails, got %v", pr.Verdict)
	}
	if pr.Enrichment == nil {
		t.Fatal("expected non-nil Enrichment on failed verdict")
	}
	if pr.Enrichment.FormulaDesc != "always(Speed < 220)" {
		t.Errorf("FormulaDesc = %q", pr.Enrichment.FormulaDesc)
	}
	// EOS enrichment now includes last-known signal values.
	if pr.Enrichment.Signals == nil {
		t.Error("expected non-nil Signals from EOS enrichment")
	} else if pr.Enrichment.Signals["Speed"] != 150 {
		t.Errorf("expected Speed=150, got %v", pr.Enrichment.Signals["Speed"])
	}
	if !strings.Contains(pr.Enrichment.EnrichedReason, "Speed = 150") {
		t.Errorf("EnrichedReason = %q, want Speed value", pr.Enrichment.EnrichedReason)
	}
}

func TestStartStream_ClearsCache(t *testing.T) {
	mock := aletheia.NewMockBackend(
		aletheia.Respond(`{"status":"success"}`), // SetProperties
		aletheia.Respond(`{"status":"success"}`), // StartStream (1st)
		// Violation then extraction for first stream
		aletheia.Respond(`{"type":"property_batch","results":[{"type":"property","status":"fails","property_index":0,"timestamp":1000,"reason":"test"}]}`),
		aletheia.Respond(`{"status":"success","values":[{"name":"Speed","value":100}],"errors":[],"absent":[]}`),
		aletheia.Respond(`{"status":"complete","results":[{"property_index":0,"status":"fails","timestamp":1000,"reason":"test"}]}`),
		aletheia.Respond(`{"status":"success","values":[{"name":"Speed","value":100}],"errors":[],"absent":[]}`), // EOS extraction
		aletheia.Respond(`{"status":"success"}`), // StartStream (2nd)
		// Violation then new extraction for same frame (cache was cleared)
		aletheia.Respond(`{"type":"property_batch","results":[{"type":"property","status":"fails","property_index":0,"timestamp":2000,"reason":"test"}]}`),
		aletheia.Respond(`{"status":"success","values":[{"name":"Speed","value":200}],"errors":[],"absent":[]}`),
	)
	c, err := aletheia.NewClient(mock)
	if err != nil {
		t.Fatal(err)
	}
	defer c.Close()

	err = c.SetProperties(ctx, []aletheia.Formula{
		aletheia.Always{Inner: aletheia.Atomic{Predicate: aletheia.LessThan{Signal: "Speed", Value: aletheia.RationalFromFloat(220)}}},
	})
	if err != nil {
		t.Fatal(err)
	}

	// First stream
	err = c.StartStream(ctx)
	if err != nil {
		t.Fatal(err)
	}
	sid, _ := aletheia.NewStandardID(0x123)
	data := aletheia.FramePayload{0xF5, 0x09, 0, 0, 0, 0, 0, 0}
	resp, err := c.SendFrame(ctx, aletheia.Timestamp{Microseconds: 1000}, sid, dlc8(), data, nil, nil)
	if err != nil {
		t.Fatal(err)
	}
	b1, ok := resp.(aletheia.PropertyBatch)
	if !ok {
		t.Fatalf("stream 1: expected PropertyBatch, got %T", resp)
	}
	v1 := b1.FirstViolation()
	if v1 == nil || v1.Enrichment == nil || v1.Enrichment.Signals["Speed"] != 100 {
		t.Fatalf("stream 1: expected Speed=100, got %+v", v1)
	}
	_, err = c.EndStream(ctx)
	if err != nil {
		t.Fatal(err)
	}

	// Second stream (cache cleared by StartStream)
	err = c.StartStream(ctx)
	if err != nil {
		t.Fatal(err)
	}
	resp, err = c.SendFrame(ctx, aletheia.Timestamp{Microseconds: 2000}, sid, dlc8(), data, nil, nil)
	if err != nil {
		t.Fatal(err)
	}
	b2, ok := resp.(aletheia.PropertyBatch)
	if !ok {
		t.Fatalf("stream 2: expected PropertyBatch, got %T", resp)
	}
	v2 := b2.FirstViolation()
	if v2 == nil || v2.Enrichment == nil || v2.Enrichment.Signals["Speed"] != 200 {
		t.Fatalf("stream 2: expected Speed=200, got %+v", v2)
	}
}

func TestFormatFormula_MetricTimeBounds(t *testing.T) {
	inner := aletheia.Atomic{Predicate: aletheia.LessThan{Signal: "S", Value: aletheia.RationalFromFloat(1)}}
	tests := []struct {
		us   int64
		want string // substring expected in formatted output
	}{
		{1500000, "1500ms"},
		{1000, "1ms"},
		{1500, "1500μs"},
		{1, "1μs"},
	}
	for _, tt := range tests {
		f := aletheia.MetricAlways{Bound: aletheia.TimeBound{Microseconds: tt.us}, Inner: inner}
		got := aletheia.FormatFormula(f)
		if !strings.Contains(got, tt.want) {
			t.Errorf("TimeBound{%d}: FormatFormula = %q, want substring %q", tt.us, got, tt.want)
		}
	}
}

func TestEndStream_EnrichmentExtractionFailure(t *testing.T) {
	mock := aletheia.NewMockBackend(
		aletheia.Respond(`{"status":"success"}`), // SetProperties
		aletheia.Respond(`{"status":"success"}`), // StartStream
		aletheia.Respond(`{"status":"ack"}`),     // SendFrame (stores frame in lastFrames)
		aletheia.Respond(`{
			"status":"complete",
			"results":[{"property_index":0,"status":"fails","timestamp":5000,"reason":"test"}]
		}`), // EndStream
		aletheia.Respond(`{"status":"error","code":"handler_no_dbc","message":"no DBC loaded"}`), // EOS extraction fails
	)
	c, err := aletheia.NewClient(mock)
	if err != nil {
		t.Fatal(err)
	}
	defer c.Close()

	if err := c.SetProperties(ctx, []aletheia.Formula{
		aletheia.Always{Inner: aletheia.Atomic{Predicate: aletheia.LessThan{Signal: "Speed", Value: aletheia.RationalFromFloat(220)}}},
	}); err != nil {
		t.Fatal(err)
	}
	if err := c.StartStream(ctx); err != nil {
		t.Fatal(err)
	}

	sid, _ := aletheia.NewStandardID(0x123)
	data := aletheia.FramePayload{0, 0, 0, 0, 0, 0, 0, 0}
	if _, err := c.SendFrame(ctx, aletheia.Timestamp{Microseconds: 1000}, sid, dlc8(), data, nil, nil); err != nil {
		t.Fatal(err)
	}

	sr, err := c.EndStream(ctx)
	if err != nil {
		t.Fatalf("EndStream: %v", err)
	}
	if len(sr.Results) != 1 {
		t.Fatalf("expected 1 result, got %d", len(sr.Results))
	}
	pr := sr.Results[0]
	if pr.Verdict != aletheia.Fails {
		t.Fatalf("expected Fails, got %v", pr.Verdict)
	}
	// Enrichment is still attempted even when extraction fails.
	if pr.Enrichment == nil {
		t.Fatal("expected non-nil Enrichment even with extraction failure")
	}
	// No signal values available — extraction failed.
	if pr.Enrichment.Signals != nil {
		t.Errorf("expected nil Signals, got %v", pr.Enrichment.Signals)
	}
	// Fallback reason format: "violated: <formula>"
	if !strings.Contains(pr.Enrichment.EnrichedReason, "violated:") {
		t.Errorf("expected fallback reason starting with 'violated:', got %q", pr.Enrichment.EnrichedReason)
	}
	if pr.Enrichment.FormulaDesc != "always(Speed < 220)" {
		t.Errorf("expected FormulaDesc='always(Speed < 220)', got %q", pr.Enrichment.FormulaDesc)
	}
}

func TestConcurrent_WithDiagnostics(t *testing.T) {
	n := 10
	// SetProperties + StartStream + n*(violation + extraction)
	var responses []aletheia.MockResponse
	responses = append(responses, aletheia.Respond(`{"status":"success"}`)) // SetProperties
	responses = append(responses, aletheia.Respond(`{"status":"success"}`)) // StartStream
	for i := 0; i < n; i++ {
		responses = append(responses, aletheia.Respond(`{"type":"property_batch","results":[{"type":"property","status":"fails","property_index":0,"timestamp":1000,"reason":"test"}]}`))
		responses = append(responses, aletheia.Respond(`{"status":"success","values":[{"name":"Speed","value":100}],"errors":[],"absent":[]}`))
	}
	mock := aletheia.NewMockBackend(responses...)
	c, err := aletheia.NewClient(mock)
	if err != nil {
		t.Fatal(err)
	}
	defer c.Close()

	err = c.SetProperties(ctx, []aletheia.Formula{
		aletheia.Always{Inner: aletheia.Atomic{Predicate: aletheia.LessThan{Signal: "Speed", Value: aletheia.RationalFromFloat(220)}}},
	})
	if err != nil {
		t.Fatal(err)
	}
	err = c.StartStream(ctx)
	if err != nil {
		t.Fatal(err)
	}

	var wg sync.WaitGroup
	for i := 0; i < n; i++ {
		wg.Add(1)
		go func(idx int) {
			defer wg.Done()
			sid, _ := aletheia.NewStandardID(uint16(0x100 + idx))
			data := aletheia.FramePayload{byte(idx), 0, 0, 0, 0, 0, 0, 0}
			_, _ = c.SendFrame(ctx, aletheia.Timestamp{Microseconds: int64(idx * 1000)}, sid, dlc8(), data, nil, nil)
		}(i)
	}
	wg.Wait()
}
