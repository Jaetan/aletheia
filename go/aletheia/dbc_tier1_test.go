package aletheia_test

import (
	"encoding/json"
	"strings"
	"testing"

	"github.com/aletheia-automotive/aletheia-go/aletheia"
)

// extractDbcObject pulls the "dbc" sub-object out of a parseDBC / validateDBC
// command envelope captured by MockBackend.Inputs().
func extractDbcObject(t *testing.T, raw string) map[string]any {
	t.Helper()
	var env map[string]any
	if err := json.Unmarshal([]byte(raw), &env); err != nil {
		t.Fatalf("failed to unmarshal envelope: %v\n%s", err, raw)
	}
	dbc, ok := env["dbc"].(map[string]any)
	if !ok {
		t.Fatalf("envelope has no 'dbc' object:\n%s", raw)
	}
	return dbc
}

// --- serialize ---

func TestSerializeDBC_EmitsTier1Metadata(t *testing.T) {
	mock := aletheia.NewMockBackend(aletheia.Respond(`{"status":"success"}`))
	c, err := aletheia.NewClient(mock)
	if err != nil {
		t.Fatal(err)
	}
	defer c.Close()

	id, _ := aletheia.NewStandardID(256)
	dlc, _ := aletheia.BytesToDLC(8)
	msg := aletheia.NewDbcMessage(id, "EngineData", dlc, "ECU", nil, nil)
	dbc := aletheia.DbcDefinition{
		Version:  "1.0",
		Messages: []aletheia.DbcMessage{msg},
		SignalGroups: []aletheia.DbcSignalGroup{
			{Name: "EngineGroup", Signals: []aletheia.SignalName{"RPM", "Coolant"}},
		},
		EnvironmentVars: []aletheia.DbcEnvironmentVar{
			{
				Name:    "AmbientTemp",
				VarType: aletheia.DbcVarTypeFloat,
				Initial: aletheia.Rational{Numerator: 25, Denominator: 1},
				Minimum: aletheia.Rational{Numerator: -40, Denominator: 1},
				Maximum: aletheia.Rational{Numerator: 125, Denominator: 1},
			},
		},
		ValueTables: []aletheia.DbcValueTable{
			{
				Name: "GearState",
				Entries: []aletheia.DbcValueEntry{
					{Value: 0, Description: "Park"},
					{Value: 1, Description: "Reverse"},
				},
			},
		},
	}

	if err := c.ParseDBC(dbc); err != nil {
		t.Fatalf("ParseDBC: %v", err)
	}

	inputs := mock.Inputs()
	if len(inputs) != 1 {
		t.Fatalf("expected 1 input, got %d", len(inputs))
	}
	dbcObj := extractDbcObject(t, inputs[0])

	groups, ok := dbcObj["signalGroups"].([]any)
	if !ok || len(groups) != 1 {
		t.Fatalf("signalGroups missing or wrong shape: %v", dbcObj["signalGroups"])
	}
	g := groups[0].(map[string]any)
	if g["name"] != "EngineGroup" {
		t.Errorf("group name: got %v, want EngineGroup", g["name"])
	}
	sigs, _ := g["signals"].([]any)
	if len(sigs) != 2 || sigs[0] != "RPM" || sigs[1] != "Coolant" {
		t.Errorf("group signals: got %v", sigs)
	}

	envVars, ok := dbcObj["environmentVars"].([]any)
	if !ok || len(envVars) != 1 {
		t.Fatalf("environmentVars missing or wrong shape: %v", dbcObj["environmentVars"])
	}
	ev := envVars[0].(map[string]any)
	if ev["name"] != "AmbientTemp" {
		t.Errorf("env var name: got %v", ev["name"])
	}
	if vt, _ := ev["varType"].(float64); int(vt) != int(aletheia.DbcVarTypeFloat) {
		t.Errorf("env var varType: got %v, want %d", ev["varType"], aletheia.DbcVarTypeFloat)
	}

	tables, ok := dbcObj["valueTables"].([]any)
	if !ok || len(tables) != 1 {
		t.Fatalf("valueTables missing or wrong shape: %v", dbcObj["valueTables"])
	}
	vt := tables[0].(map[string]any)
	if vt["name"] != "GearState" {
		t.Errorf("value table name: got %v", vt["name"])
	}
	entries, _ := vt["entries"].([]any)
	if len(entries) != 2 {
		t.Fatalf("value table entries: got %d, want 2", len(entries))
	}
}

func TestSerializeDBC_EmitsEmptyArraysWhenMetadataAbsent(t *testing.T) {
	mock := aletheia.NewMockBackend(aletheia.Respond(`{"status":"success"}`))
	c, err := aletheia.NewClient(mock)
	if err != nil {
		t.Fatal(err)
	}
	defer c.Close()

	id, _ := aletheia.NewStandardID(256)
	dlc, _ := aletheia.BytesToDLC(8)
	msg := aletheia.NewDbcMessage(id, "MinimalMsg", dlc, "ECU", nil, nil)
	dbc := aletheia.DbcDefinition{
		Version:  "1.0",
		Messages: []aletheia.DbcMessage{msg},
		// Tier 1 slices left nil
	}

	if err := c.ParseDBC(dbc); err != nil {
		t.Fatalf("ParseDBC: %v", err)
	}

	inputs := mock.Inputs()
	dbcObj := extractDbcObject(t, inputs[0])

	// Each key must be present as an empty array (match Python / C++ behavior).
	for _, key := range []string{"signalGroups", "environmentVars", "valueTables"} {
		arr, ok := dbcObj[key].([]any)
		if !ok {
			t.Errorf("%s: missing or not an array, got %T", key, dbcObj[key])
			continue
		}
		if len(arr) != 0 {
			t.Errorf("%s: expected empty array, got %d items", key, len(arr))
		}
	}
}

// --- parse ---

func TestFormatDBC_AcceptsTier1Metadata(t *testing.T) {
	mock := aletheia.NewMockBackend(aletheia.Respond(`{
		"status":"success",
		"dbc":{
			"version":"1.0",
			"messages":[{
				"id":256,"extended":false,"name":"EngineData","dlc":8,"sender":"ECU","signals":[]
			}],
			"signalGroups":[
				{"name":"EngineGroup","signals":["RPM","Coolant"]}
			],
			"environmentVars":[
				{"name":"AmbientTemp","varType":1,
				 "initial":{"numerator":25,"denominator":1},
				 "minimum":{"numerator":-40,"denominator":1},
				 "maximum":{"numerator":125,"denominator":1}}
			],
			"valueTables":[
				{"name":"GearState","entries":[
					{"value":0,"description":"Park"},
					{"value":1,"description":"Reverse"}
				]}
			]
		}
	}`))
	c, err := aletheia.NewClient(mock)
	if err != nil {
		t.Fatal(err)
	}
	defer c.Close()

	dbc, err := c.FormatDBC()
	if err != nil {
		t.Fatalf("FormatDBC: %v", err)
	}

	if len(dbc.SignalGroups) != 1 {
		t.Fatalf("SignalGroups: got %d, want 1", len(dbc.SignalGroups))
	}
	if dbc.SignalGroups[0].Name != "EngineGroup" {
		t.Errorf("group name: got %s", dbc.SignalGroups[0].Name)
	}
	if len(dbc.SignalGroups[0].Signals) != 2 {
		t.Errorf("group signal count: got %d", len(dbc.SignalGroups[0].Signals))
	}

	if len(dbc.EnvironmentVars) != 1 {
		t.Fatalf("EnvironmentVars: got %d, want 1", len(dbc.EnvironmentVars))
	}
	ev := dbc.EnvironmentVars[0]
	if ev.Name != "AmbientTemp" || ev.VarType != aletheia.DbcVarTypeFloat {
		t.Errorf("env var: got (%s, %d), want (AmbientTemp, %d)", ev.Name, ev.VarType, aletheia.DbcVarTypeFloat)
	}

	if len(dbc.ValueTables) != 1 {
		t.Fatalf("ValueTables: got %d, want 1", len(dbc.ValueTables))
	}
	vt := dbc.ValueTables[0]
	if vt.Name != "GearState" || len(vt.Entries) != 2 {
		t.Errorf("value table: got (%s, %d entries)", vt.Name, len(vt.Entries))
	}
	if vt.Entries[0].Value != 0 || vt.Entries[0].Description != "Park" {
		t.Errorf("first entry: got (%d, %s)", vt.Entries[0].Value, vt.Entries[0].Description)
	}
}

func TestFormatDBC_AcceptsMissingTier1Keys(t *testing.T) {
	mock := aletheia.NewMockBackend(aletheia.Respond(`{
		"status":"success",
		"dbc":{
			"version":"0.1",
			"messages":[]
		}
	}`))
	c, err := aletheia.NewClient(mock)
	if err != nil {
		t.Fatal(err)
	}
	defer c.Close()

	dbc, err := c.FormatDBC()
	if err != nil {
		t.Fatalf("FormatDBC: %v", err)
	}
	if dbc.SignalGroups != nil {
		t.Errorf("SignalGroups: expected nil (absent key), got %v", dbc.SignalGroups)
	}
	if dbc.EnvironmentVars != nil {
		t.Errorf("EnvironmentVars: expected nil (absent key), got %v", dbc.EnvironmentVars)
	}
	if dbc.ValueTables != nil {
		t.Errorf("ValueTables: expected nil (absent key), got %v", dbc.ValueTables)
	}
}

func TestFormatDBC_RejectsUnknownVarType(t *testing.T) {
	mock := aletheia.NewMockBackend(aletheia.Respond(`{
		"status":"success",
		"dbc":{
			"version":"0.1",
			"messages":[],
			"environmentVars":[
				{"name":"Bad","varType":99,
				 "initial":{"numerator":0,"denominator":1},
				 "minimum":{"numerator":0,"denominator":1},
				 "maximum":{"numerator":0,"denominator":1}}
			]
		}
	}`))
	c, err := aletheia.NewClient(mock)
	if err != nil {
		t.Fatal(err)
	}
	defer c.Close()

	_, err = c.FormatDBC()
	if err == nil {
		t.Fatal("expected error for unknown varType, got nil")
	}
	if !strings.Contains(err.Error(), "varType") {
		t.Errorf("error should mention varType, got: %v", err)
	}
}

func TestFormatDBC_EnvVarPreservesExactRationals(t *testing.T) {
	// Exact rational 1/3 (non-terminating binary fraction) — round-trip must
	// preserve numerator/denominator through Go's JSON decode and parseRational.
	mock := aletheia.NewMockBackend(aletheia.Respond(`{
		"status":"success",
		"dbc":{
			"version":"0.1",
			"messages":[],
			"environmentVars":[
				{"name":"OneThird","varType":1,
				 "initial":{"numerator":1,"denominator":3},
				 "minimum":{"numerator":0,"denominator":1},
				 "maximum":{"numerator":1,"denominator":1}}
			]
		}
	}`))
	c, err := aletheia.NewClient(mock)
	if err != nil {
		t.Fatal(err)
	}
	defer c.Close()

	dbc, err := c.FormatDBC()
	if err != nil {
		t.Fatalf("FormatDBC: %v", err)
	}
	if len(dbc.EnvironmentVars) != 1 {
		t.Fatalf("EnvironmentVars: got %d, want 1", len(dbc.EnvironmentVars))
	}
	ev := dbc.EnvironmentVars[0]
	// Rational preserves exact numerator/denominator through the wire round-trip.
	// 1/3 is chosen because it is a non-terminating binary fraction — any
	// float-based path would lose precision here.
	if ev.Initial.Numerator != 1 || ev.Initial.Denominator != 3 {
		t.Errorf("Initial: got %d/%d, want 1/3", ev.Initial.Numerator, ev.Initial.Denominator)
	}
	if ev.Minimum.Numerator != 0 || ev.Minimum.Denominator != 1 {
		t.Errorf("Minimum: got %d/%d, want 0/1", ev.Minimum.Numerator, ev.Minimum.Denominator)
	}
	if ev.Maximum.Numerator != 1 || ev.Maximum.Denominator != 1 {
		t.Errorf("Maximum: got %d/%d, want 1/1", ev.Maximum.Numerator, ev.Maximum.Denominator)
	}
}

func TestSerializeDBC_RoundtripThroughMock(t *testing.T) {
	// Build a DBC, serialize via ParseDBC, capture the envelope, feed the
	// serialized dbc sub-object back through a second client as a formatDBC
	// response. Checks that the wire representation is self-compatible.
	originalSend := aletheia.NewMockBackend(aletheia.Respond(`{"status":"success"}`))
	sendClient, err := aletheia.NewClient(originalSend)
	if err != nil {
		t.Fatal(err)
	}
	defer sendClient.Close()

	id, _ := aletheia.NewStandardID(100)
	dlc, _ := aletheia.BytesToDLC(8)
	msg := aletheia.NewDbcMessage(id, "Test", dlc, "X", nil, nil)
	original := aletheia.DbcDefinition{
		Version:  "1.0",
		Messages: []aletheia.DbcMessage{msg},
		SignalGroups: []aletheia.DbcSignalGroup{
			{Name: "G", Signals: []aletheia.SignalName{"A"}},
		},
		EnvironmentVars: []aletheia.DbcEnvironmentVar{
			{Name: "E", VarType: aletheia.DbcVarTypeInt,
				Initial: aletheia.Rational{Numerator: 0, Denominator: 1},
				Minimum: aletheia.Rational{Numerator: -10, Denominator: 1},
				Maximum: aletheia.Rational{Numerator: 10, Denominator: 1}},
		},
		ValueTables: []aletheia.DbcValueTable{
			{Name: "V", Entries: []aletheia.DbcValueEntry{{Value: 42, Description: "answer"}}},
		},
	}
	if err := sendClient.ParseDBC(original); err != nil {
		t.Fatalf("ParseDBC: %v", err)
	}

	envBytes := originalSend.Inputs()[0]
	var env map[string]any
	if err := json.Unmarshal([]byte(envBytes), &env); err != nil {
		t.Fatal(err)
	}
	// Re-wrap as a formatDBC response envelope.
	respEnv := map[string]any{"status": "success", "dbc": env["dbc"]}
	respBytes, err := json.Marshal(respEnv)
	if err != nil {
		t.Fatal(err)
	}

	parseMock := aletheia.NewMockBackend(aletheia.Respond(string(respBytes)))
	parseClient, err := aletheia.NewClient(parseMock)
	if err != nil {
		t.Fatal(err)
	}
	defer parseClient.Close()

	decoded, err := parseClient.FormatDBC()
	if err != nil {
		t.Fatalf("FormatDBC: %v", err)
	}
	if len(decoded.SignalGroups) != 1 || decoded.SignalGroups[0].Name != "G" {
		t.Errorf("signal group lost in round-trip: %v", decoded.SignalGroups)
	}
	if len(decoded.EnvironmentVars) != 1 || decoded.EnvironmentVars[0].VarType != aletheia.DbcVarTypeInt {
		t.Errorf("env var lost in round-trip: %v", decoded.EnvironmentVars)
	}
	if len(decoded.ValueTables) != 1 || decoded.ValueTables[0].Entries[0].Value != 42 {
		t.Errorf("value table lost in round-trip: %v", decoded.ValueTables)
	}
}
