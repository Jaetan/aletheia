//go:build cgo && linux

// SPDX-FileCopyrightText: 2025 Nicolas Pelletier
// SPDX-License-Identifier: BSD-2-Clause

// The log events this binding emits are the ones docs/LOG_EVENTS.yaml names,
// which is the vocabulary all four bindings share. The document is read here
// rather than mirrored, and the tests hold two things: the document is well
// formed, and a workflow driving the client emits nothing the document does
// not name. The Python and C++ suites hold their own bindings the same way.
//
// A few events need a setup no mock reaches: the runtime warning wants a
// second library backend, the cache-full event wants the cache bound reached,
// and the two event-injection ones want a real stream. They are not required
// to appear; the membership check covers them all the same, since it refuses
// anything the document does not name rather than requiring a list.

package aletheia_test

import (
	"context"
	"log/slog"
	"os"
	"path/filepath"
	"runtime"
	"testing"

	"gopkg.in/yaml.v3"

	"github.com/aletheia-automotive/aletheia-go/v5/aletheia"
)

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

// loadLogEvents reads the shared document, found from this source file rather
// than from the working directory, which a test may be run from anywhere.
func loadLogEvents(t *testing.T) []logEventRow {
	t.Helper()
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

// knownEvents is the document's names as a set.
func knownEvents(t *testing.T) map[string]struct{} {
	t.Helper()
	rows := loadLogEvents(t)
	known := make(map[string]struct{}, len(rows))
	for _, e := range rows {
		known[e.Name] = struct{}{}
	}
	return known
}

// unknownEvents is what a run emitted that the document does not name. It is
// the whole of the membership check, so the check itself can be tested without
// a workflow.
func unknownEvents(known map[string]struct{}, emitted []capturedRecord) []string {
	var unknown []string
	seen := map[string]struct{}{}
	for _, rec := range emitted {
		if _, ok := known[rec.event]; ok {
			continue
		}
		if _, repeated := seen[rec.event]; repeated {
			continue
		}
		seen[rec.event] = struct{}{}
		unknown = append(unknown, rec.event)
	}
	return unknown
}

// Every row names an event once, at a level the vocabulary has, and says what
// it is for. The count is held too: a row silently dropped would leave the
// membership check below passing over a smaller vocabulary.
func TestLogEventsYAML_Schema(t *testing.T) {
	events := loadLogEvents(t)
	if got, want := len(events), 16; got != want {
		t.Fatalf("the document names %d events, and the four bindings share %d", got, want)
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
			t.Errorf("events[%d] (%s): level %q is not one of debug, info or warn", i, e.Name, e.Level)
		}
		if e.Description == "" {
			t.Errorf("events[%d] (%s): missing description", i, e.Name)
		}
	}
}

// captureHandler keeps every record the binding writes. The message is the
// event name, which is how this binding logs one.
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

// A workflow through the whole client emits nothing the document does not
// name, and does reach the events a reader of this test would expect it to.
func TestLogEvents_ComprehensiveWorkflow_NoDrift(t *testing.T) {
	known := knownEvents(t)

	mock := aletheia.NewMockBackend(
		// The definition read as JSON, then the same one read as text: both
		// paths report one parsed definition.
		aletheia.Respond(dbcParsedJSON),
		aletheia.Respond(dbcParsedJSON),
		// The properties, then the stream.
		aletheia.Respond(`{"status":"success"}`),
		aletheia.Respond(`{"status":"success"}`),
		// A frame that says nothing, then one that violates, which sends the
		// client to extract the signals behind the violation.
		aletheia.Respond(`{"status":"ack"}`),
		aletheia.Respond(`{"type":"property_batch","results":[{"type":"property","status":"fails","property_index":0,"timestamp":5000,"reason":"Atomic: predicate failed"}]}`),
		aletheia.Respond(`{"status":"success","values":[{"name":"Speed","value":250}],"errors":[],"absent":[]}`),
		// The end of the stream, carrying a warning about an atom it never
		// observed, which is reported one event per warning.
		aletheia.Respond(`{
			"status":"complete",
			"results":[{"property_index":0,"status":"fails","timestamp":5000,"reason":"Atomic: predicate failed"}],
			"warnings":[{"kind":"uncached_atom","property_index":0,"detail":"UnobservedSignal"}]
		}`),
		// The extraction the end of stream asks for, which reuses what the
		// violation already put in the cache.
		aletheia.Respond(`{"status":"success","values":[{"name":"Speed","value":250}],"errors":[],"absent":[]}`),
	)

	handler := &captureHandler{}
	logger := slog.New(handler)
	c, err := aletheia.NewClient(mock, aletheia.WithLogger(logger))
	if err != nil {
		t.Fatal(err)
	}
	defer func() { _ = c.Close() }()

	if _, err := c.ParseDBC(ctx, aletheia.DBCDefinition{Version: "1.0"}); err != nil {
		t.Fatalf("ParseDBC: %v", err)
	}
	if _, err := c.ParseDBCText(ctx, dbcSourceText); err != nil {
		t.Fatalf("ParseDBCText: %v", err)
	}
	if err := c.SetProperties(ctx, []aletheia.Formula{
		aletheia.Always{Inner: aletheia.Atomic{Predicate: aletheia.LessThan{Signal: "Speed", Value: aletheia.IntRational(220)}}},
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
		t.Fatal("the workflow emitted nothing, so this test holds nothing")
	}
	for _, event := range unknownEvents(known, handler.records) {
		t.Errorf("the binding emitted %q, which docs/LOG_EVENTS.yaml does not name: "+
			"add it to the document and to the event list, or fix the call site", event)
	}

	// The floor: a workflow that stopped reaching these would leave the check
	// above passing over a handful of events, so each is required by name.
	emitted := map[string]struct{}{}
	for _, rec := range handler.records {
		emitted[rec.event] = struct{}{}
	}
	for _, want := range []string{"dbc.parsed", "properties.set", "stream.started", "frame.processed", "stream.ended", "endstream.uncached_atom"} {
		if _, ok := emitted[want]; !ok {
			t.Errorf("the workflow did not reach %q, so this test covers less than it reads as", want)
		}
	}
}

// The membership check itself, put to a name no document names and to one
// every document does. A workflow that stopped emitting anything would leave
// the test above passing, and this one would not.
func TestLogEvents_MembershipCheckFlagsWhatIsNotNamed(t *testing.T) {
	known := knownEvents(t)
	records := []capturedRecord{
		{event: "dbc.parsed"},
		{event: "sensor.drifted"},
		{event: "sensor.drifted"},
	}
	unknown := unknownEvents(known, records)
	if len(unknown) != 1 || unknown[0] != "sensor.drifted" {
		t.Errorf("the check reported %v, want the one name the document does not carry", unknown)
	}
	if len(unknownEvents(known, []capturedRecord{{event: "dbc.parsed"}})) != 0 {
		t.Error("a named event was reported as unknown")
	}
}
