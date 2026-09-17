//go:build cgo && linux

// SPDX-FileCopyrightText: 2025 Nicolas Pelletier
// SPDX-License-Identifier: BSD-2-Clause

package aletheia_test

import (
	"fmt"
	"strings"
	"sync"
	"testing"

	"github.com/Jaetan/aletheia/go/v5/aletheia"
)

// speedBelow220 is the one property most enrichment tests install.
var speedBelow220 = speedBelow(220)

// violationAt is a frame response failing property 0 at the timestamp.
func violationAt(ts int64, reason string) aletheia.MockResponse {
	return aletheia.Respond(fmt.Sprintf(`{"type":"property_batch","results":[{"type":"property","status":"fails","property_index":0,"timestamp":%d,"reason":%q}]}`, ts, reason))
}

// endStreamFailing is an end-of-stream response failing property 0.
func endStreamFailing(ts int64, reason string) aletheia.MockResponse {
	return aletheia.Respond(fmt.Sprintf(`{"status":"complete","results":[{"property_index":0,"status":"fails","timestamp":%d,"reason":%q}]}`, ts, reason))
}

// firstViolation is the enriched violation a frame response must carry.
func firstViolation(t *testing.T, resp aletheia.FrameResponse) *aletheia.PropertyResult {
	t.Helper()
	b, ok := resp.(aletheia.PropertyBatch)
	if !ok {
		t.Fatalf("expected PropertyBatch, got %T", resp)
	}
	v := b.FirstViolation()
	if v == nil {
		t.Fatalf("expected a violation in the batch, got %+v", b)
	}
	if v.Enrichment == nil {
		t.Fatal("expected the violation to be enriched")
	}
	return v
}

// The printer renders every operator and predicate in the shared display
// form, with thresholds through the kernel renderer and a binary operand in
// parentheses.
func TestFormatFormula(t *testing.T) {
	a, b, c := lt("A", 1), lt("B", 2), lt("C", 3)
	ms := aletheia.TimeBound{Microseconds: 5000}
	rat := func(n, d int64) aletheia.Rational { return aletheia.Rational{Numerator: n, Denominator: d} }
	atom := func(p aletheia.Predicate) aletheia.Formula { return aletheia.Atomic{Predicate: p} }
	cases := map[string]struct {
		f    aletheia.Formula
		want string
	}{
		"always":                    {aletheia.Always{Inner: lt("Speed", 220)}, "always(Speed < 220)"},
		"never":                     {aletheia.Never(aletheia.GreaterThan{Signal: "Speed", Value: aletheia.IntRational(100)}), "never Speed > 100"},
		"eventually":                {aletheia.Eventually{Inner: atom(aletheia.Equals{Signal: "Mode", Value: aletheia.IntRational(1)})}, "eventually(Mode = 1)"},
		"metric always":             {aletheia.MetricAlways{Bound: aletheia.TimeBound{Microseconds: 5000000}, Inner: lt("Speed", 220)}, "always within 5s (Speed < 220)"},
		"metric eventually":         {aletheia.MetricEventually{Bound: aletheia.TimeBound{Microseconds: 2000000}, Inner: atom(aletheia.Equals{Signal: "Mode", Value: aletheia.IntRational(1)})}, "eventually within 2s (Mode = 1)"},
		"next":                      {aletheia.Next{Inner: lt("Speed", 220)}, "next(Speed < 220)"},
		"weak next":                 {aletheia.WeakNext{Inner: a}, "weak_next(A < 1)"},
		"and":                       {aletheia.And{Left: lt("Speed", 220), Right: gt("RPM", 500)}, "Speed < 220 and RPM > 500"},
		"always of and":             {aletheia.Always{Inner: aletheia.And{Left: lt("Speed", 220), Right: gt("RPM", 500)}}, "always(Speed < 220 and RPM > 500)"},
		"until":                     {aletheia.Until{Left: gt("RPM", 500), Right: lt("Speed", 220)}, "RPM > 500 until Speed < 220"},
		"release":                   {aletheia.Release{Left: gt("RPM", 500), Right: lt("Speed", 220)}, "RPM > 500 release Speed < 220"},
		"or inside and":             {aletheia.And{Left: aletheia.Or{Left: a, Right: b}, Right: c}, "(A < 1 or B < 2) and C < 3"},
		"and inside or":             {aletheia.Or{Left: aletheia.And{Left: a, Right: b}, Right: c}, "(A < 1 and B < 2) or C < 3"},
		"until inside and":          {aletheia.And{Left: aletheia.Until{Left: a, Right: b}, Right: c}, "(A < 1 until B < 2) and C < 3"},
		"release inside and":        {aletheia.And{Left: aletheia.Release{Left: a, Right: b}, Right: c}, "(A < 1 release B < 2) and C < 3"},
		"metric until inside and":   {aletheia.And{Left: aletheia.MetricUntil{Bound: ms, Left: a, Right: b}, Right: c}, "(A < 1 until within 5ms B < 2) and C < 3"},
		"metric release inside and": {aletheia.And{Left: aletheia.MetricRelease{Bound: ms, Left: a, Right: b}, Right: c}, "(A < 1 release within 5ms B < 2) and C < 3"},
		"equals":                    {atom(aletheia.Equals{Signal: "S", Value: aletheia.IntRational(10)}), "S = 10"},
		"less than":                 {atom(aletheia.LessThan{Signal: "S", Value: aletheia.IntRational(10)}), "S < 10"},
		"greater than":              {atom(aletheia.GreaterThan{Signal: "S", Value: aletheia.IntRational(10)}), "S > 10"},
		"less than or equal":        {atom(aletheia.LessThanOrEqual{Signal: "S", Value: aletheia.IntRational(10)}), "S <= 10"},
		"greater than or equal":     {atom(aletheia.GreaterThanOrEqual{Signal: "S", Value: aletheia.IntRational(10)}), "S >= 10"},
		"between":                   {atom(aletheia.Between{Signal: "S", Min: aletheia.IntRational(5), Max: aletheia.IntRational(15)}), "5 <= S <= 15"},
		"changed by, positive":      {atom(aletheia.ChangedBy{Signal: "S", Delta: rat(5, 2)}), "ΔS >= 2.5"},
		"changed by, negative":      {atom(aletheia.ChangedBy{Signal: "S", Delta: aletheia.IntRational(-3)}), "ΔS <= -3"},
		"stable within":             {atom(aletheia.StableWithin{Signal: "S", Tolerance: rat(5, 2)}), "|ΔS| <= 2.5"},
		"equals, fraction":          {atom(aletheia.Equals{Signal: "S", Value: rat(1, 3)}), "S = 1/3"},
		"less than, decimal":        {atom(aletheia.LessThan{Signal: "V", Value: rat(23, 2)}), "V < 11.5"},
		"greater than, negative":    {atom(aletheia.GreaterThan{Signal: "S", Value: rat(-1, 3)}), "S > -1/3"},
		"between, fractions":        {atom(aletheia.Between{Signal: "S", Min: rat(1, 3), Max: rat(2, 3)}), "1/3 <= S <= 2/3"},
		"changed by, fraction":      {atom(aletheia.ChangedBy{Signal: "S", Delta: rat(1, 3)}), "ΔS >= 1/3"},
		"stable within, fraction":   {atom(aletheia.StableWithin{Signal: "S", Tolerance: rat(1, 7)}), "|ΔS| <= 1/7"},
	}
	for name, tc := range cases {
		t.Run(name, func(t *testing.T) {
			if got := aletheia.FormatFormula(tc.f); got != tc.want {
				t.Errorf("got %q, want %q", got, tc.want)
			}
		})
	}
}

// A time bound prints in the largest unit that divides it.
func TestFormatFormula_MetricTimeBounds(t *testing.T) {
	cases := map[int64]string{1500000: "1500ms", 1000: "1ms", 1500: "1500μs", 1: "1μs"}
	for us, want := range cases {
		got := aletheia.FormatFormula(aletheia.MetricAlways{Bound: aletheia.TimeBound{Microseconds: us}, Inner: lt("S", 1)})
		if !strings.Contains(got, want) {
			t.Errorf("TimeBound{%d}: got %q, want it to contain %q", us, got, want)
		}
	}
}

// Signals are collected once each, in order of first appearance.
func TestCollectSignals(t *testing.T) {
	cases := map[string]struct {
		f    aletheia.Formula
		want []aletheia.SignalName
	}{
		"two signals":  {aletheia.And{Left: lt("Speed", 220), Right: gt("RPM", 500)}, []aletheia.SignalName{"Speed", "RPM"}},
		"one repeated": {aletheia.And{Left: lt("Speed", 220), Right: gt("Speed", 0)}, []aletheia.SignalName{"Speed"}},
	}
	for name, tc := range cases {
		t.Run(name, func(t *testing.T) {
			got := aletheia.CollectSignals(tc.f)
			if len(got) != len(tc.want) {
				t.Fatalf("got %v, want %v", got, tc.want)
			}
			for i := range got {
				if got[i] != tc.want[i] {
					t.Errorf("got %v, want %v", got, tc.want)
				}
			}
		})
	}
}

// Every operator yields a diagnostic with a printed form and its signals.
func TestBuildDiagnostic_EveryOperator(t *testing.T) {
	s := aletheia.TimeBound{Microseconds: 1000000}
	pa, pb := lt("A", 1), gt("B", 2)
	formulas := []aletheia.Formula{
		lt("S", 1), aletheia.Not{Inner: lt("S", 1)},
		aletheia.And{Left: pa, Right: pb}, aletheia.Or{Left: pa, Right: pb},
		aletheia.Always{Inner: lt("S", 1)}, aletheia.Eventually{Inner: lt("S", 1)}, aletheia.Next{Inner: lt("S", 1)},
		aletheia.Until{Left: pa, Right: pb}, aletheia.Release{Left: pa, Right: pb},
		aletheia.MetricAlways{Bound: s, Inner: lt("S", 1)}, aletheia.MetricEventually{Bound: s, Inner: lt("S", 1)},
		aletheia.MetricUntil{Bound: s, Left: pa, Right: pb}, aletheia.MetricRelease{Bound: s, Left: pa, Right: pb},
	}
	for i, f := range formulas {
		diag := aletheia.BuildDiagnostic(f)
		if diag.FormulaDesc == "" || len(diag.Signals) == 0 {
			t.Errorf("formula %d: diagnostic %+v is incomplete", i, diag)
		}
	}
}

// The enriched reason lists the observed values of the signals the diagnostic
// names and appends the core's reason; with no value for any of them, or no
// values at all, it falls back to the formula alone.
func TestFormatEnrichedReason(t *testing.T) {
	diag := aletheia.PropertyDiagnostic{Signals: []aletheia.SignalName{"Speed", "RPM"}, FormulaDesc: "always(Speed < 220)"}
	cases := map[string]struct {
		values map[aletheia.SignalName]aletheia.Rational
		core   string
		want   string
	}{
		"values and core":         {map[aletheia.SignalName]aletheia.Rational{"Speed": aletheia.IntRational(250)}, "halt", "Speed = 250 (formula: always(Speed < 220)) [core: halt]"},
		"values without core":     {map[aletheia.SignalName]aletheia.Rational{"Speed": aletheia.IntRational(250)}, "", "Speed = 250 (formula: always(Speed < 220))"},
		"no values":               {nil, "", "violated: always(Speed < 220)"},
		"values of other signals": {map[aletheia.SignalName]aletheia.Rational{"Temp": aletheia.IntRational(80)}, "", "violated: always(Speed < 220)"},
	}
	for name, tc := range cases {
		t.Run(name, func(t *testing.T) {
			if got := aletheia.FormatEnrichedReason(diag, tc.values, tc.core); got != tc.want {
				t.Errorf("got %q, want %q", got, tc.want)
			}
		})
	}
}

// A violating frame comes back enriched with the property's printed form,
// the values extracted from the frame for the signals it names, and a
// reason listing them.
func TestSendFrame_EnrichedViolation(t *testing.T) {
	c, _ := startedClientWith(t, []aletheia.Formula{aletheia.Always{Inner: aletheia.And{Left: lt("Speed", 220), Right: gt("RPM", 500)}}},
		violationAt(2000000, "Atomic: predicate failed"), extractionOf("Speed", 245, "RPM", 3000))
	v := firstViolation(t, sendFrame(t, c, 2000000, 0xF5, 0x09, 0, 0, 0, 0, 0, 0))
	if v.Enrichment.FormulaDesc != "always(Speed < 220 and RPM > 500)" {
		t.Errorf("FormulaDesc = %q", v.Enrichment.FormulaDesc)
	}
	if len(v.Enrichment.Signals) != 2 || v.Enrichment.Signals["Speed"] != aletheia.IntRational(245) || v.Enrichment.Signals["RPM"] != aletheia.IntRational(3000) {
		t.Errorf("Signals = %v, want Speed=245 and RPM=3000", v.Enrichment.Signals)
	}
	for _, want := range []string{"Speed = 245", "RPM = 3000", "always(Speed < 220 and RPM > 500)", "[core: Atomic: predicate failed]"} {
		if !strings.Contains(v.Enrichment.EnrichedReason, want) {
			t.Errorf("EnrichedReason = %q, want it to contain %q", v.Enrichment.EnrichedReason, want)
		}
	}
	if v.Enrichment.CoreReason != "Atomic: predicate failed" {
		t.Errorf("CoreReason = %q", v.Enrichment.CoreReason)
	}
}

// The extraction for a frame is done once and served from the cache to a
// second violation on the same frame, so the mock sees one extraction.
func TestSendFrame_ExtractionCaching(t *testing.T) {
	c, mock := startedClientWith(t, []aletheia.Formula{speedBelow220},
		violationAt(1000000, "test"), extractionOf("Speed", 245), violationAt(2000000, "test"))
	firstViolation(t, sendFrame(t, c, 1000000, 0xF5, 0x09, 0, 0, 0, 0, 0, 0))
	v2 := firstViolation(t, sendFrame(t, c, 2000000, 0xF5, 0x09, 0, 0, 0, 0, 0, 0))
	if v2.Enrichment.Signals["Speed"] != aletheia.IntRational(245) {
		t.Errorf("expected the cached Speed=245, got %v", v2.Enrichment.Signals["Speed"])
	}
	if got := len(mock.Inputs()); got != 5 {
		t.Errorf("expected 5 backend calls (one extraction), got %d", got)
	}
}

// Past the cache's capacity every violation is still enriched; the
// extraction is done and not stored.
func TestSendFrame_CacheBounded(t *testing.T) {
	const frames = 257
	responses := make([]aletheia.MockResponse, 0, 2*frames)
	for range frames {
		responses = append(responses, violationAt(1000, "test"), extractionOf("Speed", 100))
	}
	c, _ := startedClientWith(t, []aletheia.Formula{speedBelow220}, responses...)
	for i := range frames {
		sid, _ := aletheia.NewStandardID(uint16(i % 2048))
		resp, err := c.SendFrame(ctx, aletheia.Timestamp{Microseconds: 1000}, sid, dlc8(), aletheia.FramePayload{byte(i), byte(i >> 8), 0, 0, 0, 0, 0, 0}, nil, nil)
		if err != nil {
			t.Fatalf("SendFrame %d: %v", i, err)
		}
		firstViolation(t, resp)
	}
}

// End of stream enriches a failed verdict from the last frame seen on each
// CAN ID; when that extraction fails the enrichment still carries the
// formula and falls back to it for the reason.
func TestEndStream_Enriched(t *testing.T) {
	cases := map[string]struct {
		extraction aletheia.MockResponse
		signals    bool
		reason     string
	}{
		"extraction succeeds": {extractionOf("Speed", 150), true, "Speed = 150"},
		"extraction fails":    {aletheia.Respond(`{"status":"error","code":"handler_no_dbc","message":"no DBC loaded"}`), false, "violated:"},
	}
	for name, tc := range cases {
		t.Run(name, func(t *testing.T) {
			c, _ := startedClientWith(t, []aletheia.Formula{speedBelow220},
				aletheia.Respond(`{"status":"ack"}`), endStreamFailing(5000000, "Atomic: predicate failed"), tc.extraction)
			sendFrame(t, c, 1000, 0, 0, 0, 0, 0, 0, 0, 0)
			sr, err := c.EndStream(ctx)
			if err != nil {
				t.Fatalf("EndStream: %v", err)
			}
			if len(sr.Results) != 1 || sr.Results[0].Verdict != aletheia.Fails || sr.Results[0].Enrichment == nil {
				t.Fatalf("expected one enriched failing verdict, got %+v", sr.Results)
			}
			e := sr.Results[0].Enrichment
			if e.FormulaDesc != "always(Speed < 220)" {
				t.Errorf("FormulaDesc = %q", e.FormulaDesc)
			}
			if tc.signals && e.Signals["Speed"] != aletheia.IntRational(150) {
				t.Errorf("Signals = %v, want Speed=150", e.Signals)
			}
			if !tc.signals && e.Signals != nil {
				t.Errorf("Signals = %v, want nil after a failed extraction", e.Signals)
			}
			if !strings.Contains(e.EnrichedReason, tc.reason) {
				t.Errorf("EnrichedReason = %q, want it to contain %q", e.EnrichedReason, tc.reason)
			}
		})
	}
}

// StartStream clears the extraction cache: the same frame in a second stream
// is extracted again.
func TestStartStream_ClearsCache(t *testing.T) {
	c, _ := startedClientWith(t, []aletheia.Formula{speedBelow220},
		violationAt(1000, "test"), extractionOf("Speed", 100),
		endStreamFailing(1000, "test"), extractionOf("Speed", 100),
		aletheia.Respond(`{"status":"success"}`),
		violationAt(2000, "test"), extractionOf("Speed", 200))
	if v := firstViolation(t, sendFrame(t, c, 1000, 0xF5, 0x09, 0, 0, 0, 0, 0, 0)); v.Enrichment.Signals["Speed"] != aletheia.IntRational(100) {
		t.Fatalf("stream 1: expected Speed=100, got %+v", v.Enrichment.Signals)
	}
	if _, err := c.EndStream(ctx); err != nil {
		t.Fatal(err)
	}
	if err := c.StartStream(ctx); err != nil {
		t.Fatal(err)
	}
	if v := firstViolation(t, sendFrame(t, c, 2000, 0xF5, 0x09, 0, 0, 0, 0, 0, 0)); v.Enrichment.Signals["Speed"] != aletheia.IntRational(200) {
		t.Fatalf("stream 2: expected Speed=200, got %+v", v.Enrichment.Signals)
	}
}

// Concurrent sends on one client with diagnostics installed all succeed and
// never race.
func TestConcurrent_WithDiagnostics(t *testing.T) {
	const n = 10
	responses := make([]aletheia.MockResponse, 0, 2*n)
	for range n {
		responses = append(responses, violationAt(1000, "test"), extractionOf("Speed", 100))
	}
	c, _ := startedClientWith(t, []aletheia.Formula{speedBelow220}, responses...)
	errs := make(chan error, n)
	var wg sync.WaitGroup
	for i := range n {
		wg.Add(1)
		go func() {
			defer wg.Done()
			sid, _ := aletheia.NewStandardID(uint16(0x100 + i))
			_, err := c.SendFrame(ctx, aletheia.Timestamp{Microseconds: int64(i * 1000)}, sid, dlc8(), aletheia.FramePayload{byte(i), 0, 0, 0, 0, 0, 0, 0}, nil, nil)
			errs <- err
		}()
	}
	wg.Wait()
	close(errs)
	for err := range errs {
		if err != nil {
			t.Errorf("a concurrent send failed: %v", err)
		}
	}
}
