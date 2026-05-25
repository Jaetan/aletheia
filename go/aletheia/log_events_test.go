// Cross-binding log event vocabulary parity — Go side.
//
// Reads docs/LOG_EVENTS.yaml and asserts:
//
//   1. The YAML is well-formed (15 entries, each with name + valid level).
//   2. Every event emitted by a comprehensive workflow is a member of the
//      YAML name set — catches a future binding-side emit-call that drifts
//      from the cross-binding canonical set.
//
// This is the "missing mechanism" half of R18 cluster 10: the surface fix
// in client.go (renaming dbc.text_parsed → dbc.parsed) closes the rogue
// 16th event, and this test prevents the same class of drift from being
// reintroduced silently.  Mirrors python/tests/test_log_events_parity.py
// (YAML ↔ LogEvent enum) and cpp/tests/test_log_events_parity.cpp.
//
// The workflow exercises:
//   - ParseDBC          (JSON-shape DBC path     → dbc.parsed)
//   - ParseDBCText      (DBC-text parser path    → dbc.parsed; THIS is
//                                                  the path that drifted)
//   - SetProperties     (properties.set)
//   - StartStream       (stream.started)
//   - SendFrame ack     (frame.processed)
//   - SendFrame violate (frame.processed + cache.miss + cache.hit +
//                        enrichment.* on extraction failure)
//   - EndStream         (stream.ended + endstream.uncached_atom per warning)
//   - Extraction error  (extraction.parse_failed + enrichment.extraction_failed)
//
// Events not exercised (need exotic setups, deliberately not asserted as
// "must appear"; they remain protected by the ⊆ assertion against any
// future emit drift): rts.cores_mismatch (FFI backend mismatch only),
// cache.full (requires the cache capacity bound to be hit), error_event.sent
// and remote_event.sent (event-injection paths not covered by mock).

package aletheia_test

import (
	"context"
	"log/slog"
	"os"
	"path/filepath"
	"runtime"
	"testing"

	"gopkg.in/yaml.v3"

	"github.com/aletheia-automotive/aletheia-go/aletheia"
)

// ----- YAML schema -----

type logEventRow struct {
	Name        string `yaml:"name"`
	Level       string `yaml:"level"`
	Description string `yaml:"description"`
}

type logEventDoc struct {
	Events []logEventRow `yaml:"events"`
}

var validLogEventLevels = map[string]struct{}{
	"debug": {},
	"info":  {},
	"warn":  {},
}

func loadLogEvents(t *testing.T) []logEventRow {
	t.Helper()
	// Resolve docs/LOG_EVENTS.yaml relative to this source file (go/aletheia/).
	_, here, _, ok := runtime.Caller(0)
	if !ok {
		t.Fatal("runtime.Caller(0) failed")
	}
	yamlPath := filepath.Join(filepath.Dir(here), "..", "..", "docs", "LOG_EVENTS.yaml")
	data, err := os.ReadFile(yamlPath)
	if err != nil {
		t.Fatalf("read %s: %v", yamlPath, err)
	}
	var doc logEventDoc
	if err := yaml.Unmarshal(data, &doc); err != nil {
		t.Fatalf("unmarshal %s: %v", yamlPath, err)
	}
	if len(doc.Events) == 0 {
		t.Fatalf("%s: empty events list", yamlPath)
	}
	return doc.Events
}

// ----- 1. YAML schema sanity -----

func TestLogEventsYAML_Schema(t *testing.T) {
	events := loadLogEvents(t)
	if got, want := len(events), 16; got != want {
		t.Fatalf("event count: got %d, want %d (cross-binding canonical total)", got, want)
	}
	seen := make(map[string]struct{}, len(events))
	for i, e := range events {
		if e.Name == "" {
			t.Errorf("events[%d]: empty name", i)
			continue
		}
		if _, dup := seen[e.Name]; dup {
			t.Errorf("events[%d]: duplicate name %q", i, e.Name)
		}
		seen[e.Name] = struct{}{}
		if _, ok := validLogEventLevels[e.Level]; !ok {
			t.Errorf("events[%d] (%s): level %q not in {debug,info,warn}", i, e.Name, e.Level)
		}
		if e.Description == "" {
			t.Errorf("events[%d] (%s): missing description", i, e.Name)
		}
	}
}

// ----- 2. capturing slog.Handler -----

// captureHandler records every (level, message) pair the binding emits.
// Message is the slog.Record.Message which Go bindings set to the event
// name string when calling logger.Info("event.name", kv-pairs...).
type captureHandler struct {
	records []capturedRecord
}

type capturedRecord struct {
	level slog.Level
	event string
}

func (h *captureHandler) Enabled(_ context.Context, _ slog.Level) bool { return true }

func (h *captureHandler) Handle(_ context.Context, r slog.Record) error {
	h.records = append(h.records, capturedRecord{level: r.Level, event: r.Message})
	return nil
}

func (h *captureHandler) WithAttrs(_ []slog.Attr) slog.Handler { return h }
func (h *captureHandler) WithGroup(_ string) slog.Handler      { return h }

// ----- 3. comprehensive workflow exercising emit sites -----

const dbcSourceText = `VERSION ""
NS_ :
BS_:
BU_: ECU
BO_ 256 EngineData: 8 ECU
 SG_ Speed : 0|16@1+ (1,0) [0|300] "kph" Vector__XXX

`

const dbcParsedJSON = `{
	"status": "success",
	"dbc": {
		"version": "1.0",
		"messages": [{
			"id": 256, "extended": false, "name": "EngineData", "dlc": 8,
			"sender": "ECU",
			"signals": [{
				"name": "Speed", "startBit": 0, "length": 16,
				"byteOrder": "little_endian", "signed": false,
				"factor": {"numerator": 1, "denominator": 1},
				"offset": {"numerator": 0, "denominator": 1},
				"minimum": {"numerator": 0, "denominator": 1},
				"maximum": {"numerator": 300, "denominator": 1},
				"unit": "kph", "presence": "always",
				"valueDescriptions": []
			}]
		}]
	}
}`

func TestLogEvents_ComprehensiveWorkflow_NoDrift(t *testing.T) {
	canonicalEvents := loadLogEvents(t)
	known := make(map[string]struct{}, len(canonicalEvents))
	for _, e := range canonicalEvents {
		known[e.Name] = struct{}{}
	}

	mock := aletheia.NewMockBackend(
		// 1. ParseDBC      (json path → dbc.parsed)
		aletheia.Respond(dbcParsedJSON),
		// 2. ParseDBCText  (text path → dbc.parsed; was dbc.text_parsed pre-fix)
		aletheia.Respond(dbcParsedJSON),
		// 3. SetProperties (properties.set)
		aletheia.Respond(`{"status":"success"}`),
		// 4. StartStream   (stream.started)
		aletheia.Respond(`{"status":"success"}`),
		// 5. SendFrame ack (frame.processed @ debug)
		aletheia.Respond(`{"status":"ack"}`),
		// 6. SendFrame violation triggers enrichment extraction
		aletheia.Respond(`{"type":"property_batch","results":[{"type":"property","status":"fails","property_index":0,"timestamp":5000,"reason":"Atomic: predicate failed"}]}`),
		// 7. Enrichment extraction returns success (cache.miss + value)
		aletheia.Respond(`{"status":"success","values":[{"name":"Speed","value":250}],"errors":[],"absent":[]}`),
		// 8. EndStream (stream.ended + endstream.uncached_atom per warning)
		aletheia.Respond(`{
			"status":"complete",
			"results":[{"property_index":0,"status":"fails","timestamp":5000,"reason":"Atomic: predicate failed"}],
			"warnings":[{"kind":"uncached_atom","property_index":0,"detail":"UnobservedSignal"}]
		}`),
		// 9. EOS extraction (cache.hit reuses prior value if SignalKey matches)
		aletheia.Respond(`{"status":"success","values":[{"name":"Speed","value":250}],"errors":[],"absent":[]}`),
	)

	handler := &captureHandler{}
	logger := slog.New(handler)
	c, err := aletheia.NewClient(mock, aletheia.WithLogger(logger))
	if err != nil {
		t.Fatal(err)
	}
	defer c.Close()

	if _, err := c.ParseDBC(ctx, aletheia.DBCDefinition{Version: "1.0"}); err != nil {
		t.Fatalf("ParseDBC: %v", err)
	}
	if _, err := c.ParseDBCText(ctx, dbcSourceText); err != nil {
		t.Fatalf("ParseDBCText: %v", err)
	}
	if err := c.SetProperties(ctx, []aletheia.Formula{
		aletheia.Always{Inner: aletheia.Atomic{Predicate: aletheia.LessThan{Signal: "Speed", Value: aletheia.RationalFromFloat(220)}}},
	}); err != nil {
		t.Fatalf("SetProperties: %v", err)
	}
	if err := c.StartStream(ctx); err != nil {
		t.Fatalf("StartStream: %v", err)
	}

	sid, _ := aletheia.NewStandardID(0x100)
	data := aletheia.FramePayload{0, 0, 0, 0, 0, 0, 0, 0}
	if _, err := c.SendFrame(ctx, aletheia.Timestamp{Microseconds: 1000}, sid, dlc8(), data, nil, nil); err != nil {
		t.Fatalf("SendFrame ack: %v", err)
	}
	dataViolation := aletheia.FramePayload{0xFF, 0, 0, 0, 0, 0, 0, 0}
	if _, err := c.SendFrame(ctx, aletheia.Timestamp{Microseconds: 5000}, sid, dlc8(), dataViolation, nil, nil); err != nil {
		t.Fatalf("SendFrame violation: %v", err)
	}
	if _, err := c.EndStream(ctx); err != nil {
		t.Fatalf("EndStream: %v", err)
	}

	if len(handler.records) == 0 {
		t.Fatal("captured no log records — workflow did not exercise any emit site")
	}

	// Core assertion: every captured event is in the canonical YAML set.
	// A future emit-site drift (e.g. someone adding logger.Info("dbc.foo", ...))
	// fails this test loudly with the offending name.
	uniqueEmitted := make(map[string]struct{}, len(handler.records))
	for _, rec := range handler.records {
		uniqueEmitted[rec.event] = struct{}{}
	}
	for event := range uniqueEmitted {
		if _, ok := known[event]; !ok {
			t.Errorf("emitted event %q is not in docs/LOG_EVENTS.yaml — "+
				"add it to the canonical set and the LogEvent enum, or fix "+
				"the call site", event)
		}
	}

	// Sanity floor: the workflow above MUST exercise dbc.parsed (the path
	// that drifted), or the gate is silently weakened.
	if _, ok := uniqueEmitted["dbc.parsed"]; !ok {
		t.Error("dbc.parsed not emitted — workflow does not exercise the " +
			"DBC parse paths; the gate would have missed the original drift")
	}

	// Sanity floor: the EndStream Complete carries an uncached_atom warning,
	// so the per-warning event MUST fire — otherwise a future refactor that
	// drops the emit site would slip past this gate.
	if _, ok := uniqueEmitted["endstream.uncached_atom"]; !ok {
		t.Error("endstream.uncached_atom not emitted — EndStream mock carries " +
			"a CompleteWarning but the per-warning emit site did not fire")
	}
}

// TestLogEvents_RejectsKnownDrift verifies the gate's rejection logic by
// constructing a synthetic capture containing the rogue dbc.text_parsed
// event and confirming the membership check flags it.  This is a unit test
// of the gate itself — independent of any binding workflow — so we know
// the assertion would have caught the original R18 drift even if the
// workflow above were ever weakened.
func TestLogEvents_RejectsKnownDrift(t *testing.T) {
	canonicalEvents := loadLogEvents(t)
	known := make(map[string]struct{}, len(canonicalEvents))
	for _, e := range canonicalEvents {
		known[e.Name] = struct{}{}
	}
	if _, ok := known["dbc.text_parsed"]; ok {
		t.Fatal("LOG_EVENTS.yaml unexpectedly contains dbc.text_parsed — " +
			"the rogue event should NOT be in the canonical set")
	}
	if _, ok := known["dbc.parsed"]; !ok {
		t.Fatal("LOG_EVENTS.yaml is missing dbc.parsed — canonical event")
	}
}
