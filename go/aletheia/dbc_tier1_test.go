// SPDX-FileCopyrightText: 2025 Nicolas Pelletier
// SPDX-License-Identifier: BSD-2-Clause

package aletheia_test

import (
	"encoding/json"
	"testing"

	"github.com/aletheia-automotive/aletheia-go/aletheia"
)

// dbcObjectSent is the "dbc" object of the one command the mock recorded.
func dbcObjectSent(t *testing.T, mock *aletheia.MockBackend) map[string]any {
	t.Helper()
	inputs := mock.Inputs()
	if len(inputs) != 1 {
		t.Fatalf("expected 1 input, got %d", len(inputs))
	}
	var env map[string]any
	if err := json.Unmarshal([]byte(inputs[0]), &env); err != nil {
		t.Fatalf("the command is not JSON: %v\n%s", err, inputs[0])
	}
	dbc, ok := env["dbc"].(map[string]any)
	if !ok {
		t.Fatalf("the command has no dbc object:\n%s", inputs[0])
	}
	return dbc
}

// serialisedDBC sends the definition through ParseDBC on a mock and returns
// the dbc object the serializer wrote.
func serialisedDBC(t *testing.T, dbc aletheia.DBCDefinition) map[string]any {
	t.Helper()
	c, mock := mockClient(t, aletheia.RespondParseDBC(dbc))
	if _, err := c.ParseDBC(ctx, dbc); err != nil {
		t.Fatalf("ParseDBC: %v", err)
	}
	return dbcObjectSent(t, mock)
}

// roundTripThroughMock serialises the definition through ParseDBC, then feeds
// the serialized object back as a FormatDBC response and decodes it, so the
// wire form the binding writes is one it reads.
func roundTripThroughMock(t *testing.T, dbc aletheia.DBCDefinition) *aletheia.DBCDefinition {
	t.Helper()
	resp, err := json.Marshal(map[string]any{"status": "success", "dbc": serialisedDBC(t, dbc)})
	if err != nil {
		t.Fatal(err)
	}
	c, _ := mockClient(t, aletheia.Respond(string(resp)))
	decoded, err := c.FormatDBC(ctx)
	if err != nil {
		t.Fatalf("FormatDBC: %v", err)
	}
	return decoded
}

// minimalMessage is one message with no signals, built through the constructor.
func minimalMessage(t *testing.T, name aletheia.MessageName) aletheia.DBCMessage {
	t.Helper()
	dlc, err := aletheia.BytesToDLC(8)
	if err != nil {
		t.Fatal(err)
	}
	return aletheia.NewDBCMessage(standardID(t, 256), name, dlc, "ECU", nil, nil)
}

// tier1DBC carries one of each tier 1 metadata slice.
func tier1DBC(t *testing.T) aletheia.DBCDefinition {
	t.Helper()
	return aletheia.DBCDefinition{
		Version:      "1.0",
		Messages:     []aletheia.DBCMessage{minimalMessage(t, "EngineData")},
		SignalGroups: []aletheia.DBCSignalGroup{{Name: "EngineGroup", Signals: []aletheia.SignalName{"RPM", "Coolant"}}},
		EnvironmentVars: []aletheia.DBCEnvironmentVar{{
			Name: "AmbientTemp", VarType: aletheia.DBCVarTypeFloat,
			Initial: aletheia.IntRational(25), Minimum: aletheia.IntRational(-40), Maximum: aletheia.IntRational(125),
		}},
		ValueTables: []aletheia.DBCValueTable{{Name: "GearState", Entries: []aletheia.DBCValueEntry{{Value: 0, Description: "Park"}, {Value: 1, Description: "Reverse"}}}},
	}
}

// The serializer writes the three tier 1 slices under the wire's names with
// their contents.
func TestSerializeDBC_EmitsTier1Metadata(t *testing.T) {
	dbcObj := serialisedDBC(t, tier1DBC(t))

	groups, ok := dbcObj["signalGroups"].([]any)
	if !ok || len(groups) != 1 {
		t.Fatalf("signalGroups missing or wrong shape: %v", dbcObj["signalGroups"])
	}
	g := groups[0].(map[string]any)
	sigs, _ := g["signals"].([]any)
	if g["name"] != "EngineGroup" || len(sigs) != 2 || sigs[0] != "RPM" || sigs[1] != "Coolant" {
		t.Errorf("group: got %v", g)
	}

	envVars, ok := dbcObj["environmentVars"].([]any)
	if !ok || len(envVars) != 1 {
		t.Fatalf("environmentVars missing or wrong shape: %v", dbcObj["environmentVars"])
	}
	ev := envVars[0].(map[string]any)
	if vt, _ := ev["varType"].(float64); ev["name"] != "AmbientTemp" || int(vt) != int(aletheia.DBCVarTypeFloat) {
		t.Errorf("env var: got %v", ev)
	}

	tables, ok := dbcObj["valueTables"].([]any)
	if !ok || len(tables) != 1 {
		t.Fatalf("valueTables missing or wrong shape: %v", dbcObj["valueTables"])
	}
	vt := tables[0].(map[string]any)
	entries, _ := vt["entries"].([]any)
	if vt["name"] != "GearState" || len(entries) != 2 {
		t.Errorf("value table: got %v", vt)
	}
}

// Absent tier 1 metadata is written as three empty arrays, as the Python and
// C++ bindings write it.
func TestSerializeDBC_EmitsEmptyArraysWhenMetadataAbsent(t *testing.T) {
	dbcObj := serialisedDBC(t, aletheia.DBCDefinition{Version: "1.0", Messages: []aletheia.DBCMessage{minimalMessage(t, "MinimalMsg")}})
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

// The decoder reads the three tier 1 slices, and an exact rational in an
// environment variable (1/3 has no finite binary expansion) survives.
func TestFormatDBC_AcceptsTier1Metadata(t *testing.T) {
	c, _ := mockClient(t, aletheia.Respond(`{"status":"success","dbc":{"version":"1.0",
		"messages":[{"id":256,"extended":false,"name":"EngineData","dlc":8,"sender":"ECU","signals":[]}],
		"signalGroups":[{"name":"EngineGroup","signals":["RPM","Coolant"]}],
		"environmentVars":[{"name":"AmbientTemp","varType":1,"initial":{"numerator":1,"denominator":3},"minimum":{"numerator":-40,"denominator":1},"maximum":{"numerator":125,"denominator":1}}],
		"valueTables":[{"name":"GearState","entries":[{"value":0,"description":"Park"},{"value":1,"description":"Reverse"}]}]}}`))
	dbc, err := c.FormatDBC(ctx)
	if err != nil {
		t.Fatalf("FormatDBC: %v", err)
	}
	if len(dbc.SignalGroups) != 1 || dbc.SignalGroups[0].Name != "EngineGroup" || len(dbc.SignalGroups[0].Signals) != 2 {
		t.Errorf("signal groups: got %+v", dbc.SignalGroups)
	}
	if len(dbc.EnvironmentVars) != 1 {
		t.Fatalf("EnvironmentVars: got %d, want 1", len(dbc.EnvironmentVars))
	}
	ev := dbc.EnvironmentVars[0]
	if ev.Name != "AmbientTemp" || ev.VarType != aletheia.DBCVarTypeFloat {
		t.Errorf("env var: got (%s, %s)", ev.Name, ev.VarType)
	}
	if ev.Initial != (aletheia.Rational{Numerator: 1, Denominator: 3}) || ev.Minimum != aletheia.IntRational(-40) || ev.Maximum != aletheia.IntRational(125) {
		t.Errorf("env var bounds: got %v %v %v, want 1/3 -40 125", ev.Initial, ev.Minimum, ev.Maximum)
	}
	if len(dbc.ValueTables) != 1 || dbc.ValueTables[0].Name != "GearState" || len(dbc.ValueTables[0].Entries) != 2 ||
		dbc.ValueTables[0].Entries[0] != (aletheia.DBCValueEntry{Value: 0, Description: "Park"}) {
		t.Errorf("value tables: got %+v", dbc.ValueTables)
	}
}

// Tier 1 keys absent from a response decode to nil slices.
func TestFormatDBC_AcceptsMissingTier1Keys(t *testing.T) {
	c, _ := mockClient(t, aletheia.Respond(`{"status":"success","dbc":{"version":"0.1","messages":[]}}`))
	dbc, err := c.FormatDBC(ctx)
	if err != nil {
		t.Fatalf("FormatDBC: %v", err)
	}
	if dbc.SignalGroups != nil || dbc.EnvironmentVars != nil || dbc.ValueTables != nil {
		t.Errorf("expected nil slices for absent keys, got %v %v %v", dbc.SignalGroups, dbc.EnvironmentVars, dbc.ValueTables)
	}
}

// A variable type tag outside the DBC text's three is a protocol error that
// names the field.
func TestFormatDBC_RejectsUnknownVarType(t *testing.T) {
	c, _ := mockClient(t, aletheia.Respond(`{"status":"success","dbc":{"version":"0.1","messages":[],
		"environmentVars":[{"name":"Bad","varType":99,"initial":{"numerator":0,"denominator":1},"minimum":{"numerator":0,"denominator":1},"maximum":{"numerator":0,"denominator":1}}]}}`))
	_, err := c.FormatDBC(ctx)
	requireKind(t, err, aletheia.ErrProtocol)
	requireErrorContains(t, err, "varType")
}

// What the serializer writes for tier 1 metadata, the decoder reads back.
func TestSerializeDBC_RoundtripThroughMock(t *testing.T) {
	decoded := roundTripThroughMock(t, tier1DBC(t))
	if len(decoded.SignalGroups) != 1 || decoded.SignalGroups[0].Name != "EngineGroup" {
		t.Errorf("signal group lost in round-trip: %v", decoded.SignalGroups)
	}
	if len(decoded.EnvironmentVars) != 1 || decoded.EnvironmentVars[0].VarType != aletheia.DBCVarTypeFloat || decoded.EnvironmentVars[0].Initial != aletheia.IntRational(25) {
		t.Errorf("env var lost in round-trip: %v", decoded.EnvironmentVars)
	}
	if len(decoded.ValueTables) != 1 || len(decoded.ValueTables[0].Entries) != 2 || decoded.ValueTables[0].Entries[1].Description != "Reverse" {
		t.Errorf("value table lost in round-trip: %v", decoded.ValueTables)
	}
}
