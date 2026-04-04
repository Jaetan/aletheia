package aletheia_test

import (
	"bytes"
	"strings"
	"testing"

	"github.com/aletheia-automotive/aletheia-go/aletheia"
)

func TestParseDBC(t *testing.T) {
	mock := aletheia.NewMockBackend(
		aletheia.Respond(`{"status":"success"}`),
	)
	c, err := aletheia.NewClient(mock)
	if err != nil {
		t.Fatal(err)
	}
	defer c.Close()

	err = c.ParseDBC(testDBC())
	if err != nil {
		t.Fatalf("ParseDBC: %v", err)
	}
	if len(mock.Inputs) != 1 {
		t.Fatalf("expected 1 input, got %d", len(mock.Inputs))
	}
	// AlwaysPresent signals must emit "presence":"always" for cross-language parity.
	if !strings.Contains(mock.Inputs[0], `"presence":"always"`) {
		t.Errorf("expected presence field in serialized DBC, got: %s", mock.Inputs[0])
	}
}

func TestValidateDBC_NoErrors(t *testing.T) {
	mock := aletheia.NewMockBackend(
		aletheia.Respond(`{"status":"validation","has_errors":false,"issues":[]}`),
	)
	c, err := aletheia.NewClient(mock)
	if err != nil {
		t.Fatal(err)
	}
	defer c.Close()

	result, err := c.ValidateDBC(testDBC())
	if err != nil {
		t.Fatalf("ValidateDBC: %v", err)
	}
	if result.HasErrors {
		t.Error("expected no errors")
	}
	if len(result.Issues) != 0 {
		t.Errorf("expected 0 issues, got %d", len(result.Issues))
	}
}

func TestValidateDBC_WithIssues(t *testing.T) {
	mock := aletheia.NewMockBackend(
		aletheia.Respond(`{
			"status":"validation",
			"has_errors":true,
			"issues":[
				{"severity":"error","code":"factor_zero","detail":"Signal Speed has zero factor"},
				{"severity":"warning","code":"empty_message","detail":"Message Diag has no signals"}
			]
		}`),
	)
	c, err := aletheia.NewClient(mock)
	if err != nil {
		t.Fatal(err)
	}
	defer c.Close()

	result, err := c.ValidateDBC(testDBC())
	if err != nil {
		t.Fatalf("ValidateDBC: %v", err)
	}
	if !result.HasErrors {
		t.Error("expected has_errors=true")
	}
	if len(result.Issues) != 2 {
		t.Fatalf("expected 2 issues, got %d", len(result.Issues))
	}
	if result.Issues[0].Code != aletheia.IssueFactorZero {
		t.Errorf("expected factor_zero, got %s", result.Issues[0].Code)
	}
	if result.Issues[0].Severity != aletheia.SeverityError {
		t.Error("expected error severity")
	}
	if result.Issues[1].Severity != aletheia.SeverityWarning {
		t.Error("expected warning severity")
	}
}

func TestFormatDBC(t *testing.T) {
	mock := aletheia.NewMockBackend(
		aletheia.Respond(`{
			"status":"success",
			"dbc":{
				"version":"1.0",
				"messages":[{
					"id":291,"extended":false,"name":"EngineData","dlc":8,"sender":"ECU",
					"signals":[{
						"name":"Speed","startBit":0,"length":16,"byteOrder":"little_endian",
						"signed":false,"factor":{"numerator":1,"denominator":10},"offset":0,"minimum":0,"maximum":300,"unit":"km/h"
					}]
				}]
			}
		}`),
	)
	c, err := aletheia.NewClient(mock)
	if err != nil {
		t.Fatal(err)
	}
	defer c.Close()

	dbc, err := c.FormatDBC()
	if err != nil {
		t.Fatalf("FormatDBC: %v", err)
	}
	if dbc.Version != "1.0" {
		t.Errorf("expected version 1.0, got %s", dbc.Version)
	}
	if len(dbc.Messages) != 1 {
		t.Fatalf("expected 1 message, got %d", len(dbc.Messages))
	}
	if dbc.Messages[0].Name != "EngineData" {
		t.Errorf("expected EngineData, got %s", dbc.Messages[0].Name)
	}
	if len(dbc.Messages[0].Signals) != 1 {
		t.Fatalf("expected 1 signal, got %d", len(dbc.Messages[0].Signals))
	}
	if dbc.Messages[0].Signals[0].Name != "Speed" {
		t.Errorf("expected Speed, got %s", dbc.Messages[0].Signals[0].Name)
	}
}

func TestExtractSignals(t *testing.T) {
	mock := aletheia.NewMockBackend(
		aletheia.Respond(`{
			"status":"success",
			"values":[{"name":"Speed","value":120.5}],
			"errors":[],
			"absent":["Temp"]
		}`),
	)
	c, err := aletheia.NewClient(mock)
	if err != nil {
		t.Fatal(err)
	}
	defer c.Close()

	sid, _ := aletheia.NewStandardID(0x123)
	result, err := c.ExtractSignals(sid, dlc8(), aletheia.FramePayload{0xDE, 0xAD, 0xBE, 0xEF, 0, 0, 0, 0})
	if err != nil {
		t.Fatalf("ExtractSignals: %v", err)
	}
	if len(result.Values) != 1 {
		t.Fatalf("expected 1 value, got %d", len(result.Values))
	}
	if result.Values[0].Name != "Speed" {
		t.Errorf("expected Speed, got %s", result.Values[0].Name)
	}
	if result.Values[0].Value != 120.5 {
		t.Errorf("expected 120.5, got %f", result.Values[0].Value)
	}

	// Test Get helper
	val, ok := result.Get("Speed")
	if !ok {
		t.Error("Get(Speed) should succeed")
	}
	if val != 120.5 {
		t.Errorf("Get(Speed) = %f, want 120.5", val)
	}
	_, ok = result.Get("Nonexistent")
	if ok {
		t.Error("Get(Nonexistent) should return false")
	}

	if len(result.Absent) != 1 || result.Absent[0] != "Temp" {
		t.Errorf("expected absent=[Temp], got %v", result.Absent)
	}
}

func TestExtractSignals_RationalValue(t *testing.T) {
	mock := aletheia.NewMockBackend(
		aletheia.Respond(`{
			"status":"success",
			"values":[{"name":"Ratio","value":{"numerator":1,"denominator":3}}],
			"errors":[],
			"absent":[]
		}`),
	)
	c, err := aletheia.NewClient(mock)
	if err != nil {
		t.Fatal(err)
	}
	defer c.Close()

	sid, _ := aletheia.NewStandardID(0x100)
	result, err := c.ExtractSignals(sid, dlc8(), aletheia.FramePayload{0, 0, 0, 0, 0, 0, 0, 0})
	if err != nil {
		t.Fatalf("ExtractSignals: %v", err)
	}
	val, ok := result.Get("Ratio")
	if !ok {
		t.Fatal("expected Ratio signal")
	}
	expected := 1.0 / 3.0
	if diff := val - aletheia.PhysicalValue(expected); diff > 0.0001 || diff < -0.0001 {
		t.Errorf("expected ~%f, got %f", expected, val)
	}
}

func TestBuildFrame(t *testing.T) {
	mock := aletheia.NewMockBackend(
		aletheia.Respond(`{"status":"success"}`), // ParseDBC
		aletheia.Respond(`{
			"status":"success",
			"data":[222,173,190,239,0,0,0,0]
		}`),
	)
	c, err := aletheia.NewClient(mock)
	if err != nil {
		t.Fatal(err)
	}
	defer c.Close()

	if err := c.ParseDBC(testDBC()); err != nil {
		t.Fatal(err)
	}
	sid, _ := aletheia.NewStandardID(0x123)
	dlc, _ := aletheia.NewDLC(8)
	payload, err := c.BuildFrame(sid, []aletheia.SignalValue{
		{Name: "Speed", Value: 120.5},
	}, dlc)
	if err != nil {
		t.Fatalf("BuildFrame: %v", err)
	}
	expected := aletheia.FramePayload{0xDE, 0xAD, 0xBE, 0xEF, 0, 0, 0, 0}
	if !bytes.Equal(payload, expected) {
		t.Errorf("expected %v, got %v", expected, payload)
	}
}

func TestUpdateFrame(t *testing.T) {
	mock := aletheia.NewMockBackend(
		aletheia.Respond(`{"status":"success"}`), // ParseDBC
		aletheia.Respond(`{
			"status":"success",
			"data":[0,100,0,0,0,0,0,0]
		}`),
	)
	c, err := aletheia.NewClient(mock)
	if err != nil {
		t.Fatal(err)
	}
	defer c.Close()

	if err := c.ParseDBC(testDBC()); err != nil {
		t.Fatal(err)
	}
	sid, _ := aletheia.NewStandardID(0x123)
	data := aletheia.FramePayload{0, 0, 0, 0, 0, 0, 0, 0}
	payload, err := c.UpdateFrame(sid, dlc8(), data, []aletheia.SignalValue{
		{Name: "Speed", Value: 100.0},
	})
	if err != nil {
		t.Fatalf("UpdateFrame: %v", err)
	}
	if payload[1] != 100 {
		t.Errorf("expected byte[1]=100, got %d", payload[1])
	}
}

func TestExtendedIDInDBC(t *testing.T) {
	mock := aletheia.NewMockBackend(
		aletheia.Respond(`{"status":"success"}`),
	)
	c, err := aletheia.NewClient(mock)
	if err != nil {
		t.Fatal(err)
	}
	defer c.Close()

	eid, _ := aletheia.NewExtendedID(0x18FEF100)
	dlc, _ := aletheia.NewDLC(8)
	dbc := aletheia.DbcDefinition{
		Version: "",
		Messages: []aletheia.DbcMessage{{
			ID: eid, Name: "J1939Msg", DLC: dlc, Sender: "Node",
			Signals: nil,
		}},
	}
	err = c.ParseDBC(dbc)
	if err != nil {
		t.Fatalf("ParseDBC with extended ID: %v", err)
	}
}

func TestMultiplexedSignal(t *testing.T) {
	mock := aletheia.NewMockBackend(
		aletheia.Respond(`{"status":"success"}`),
	)
	c, err := aletheia.NewClient(mock)
	if err != nil {
		t.Fatal(err)
	}
	defer c.Close()

	sid, _ := aletheia.NewStandardID(0x200)
	dlc, _ := aletheia.NewDLC(8)
	dbc := aletheia.DbcDefinition{
		Version: "",
		Messages: []aletheia.DbcMessage{{
			ID: sid, Name: "MuxMsg", DLC: dlc, Sender: "ECU",
			Signals: []aletheia.DbcSignal{
				{
					Name: "MuxSelector", StartBit: 0, BitLength: 8,
					ByteOrder: aletheia.LittleEndian, Presence: aletheia.AlwaysPresent{},
					Factor: aletheia.Rational{Numerator: 1, Denominator: 1}, Offset: aletheia.Rational{Numerator: 0, Denominator: 1}, Minimum: aletheia.Rational{Numerator: 0, Denominator: 1}, Maximum: aletheia.Rational{Numerator: 3, Denominator: 1}, Unit: "",
				},
				{
					Name: "TempA", StartBit: 8, BitLength: 16,
					ByteOrder: aletheia.LittleEndian,
					Presence:  aletheia.Multiplexed{Multiplexor: "MuxSelector", MuxValue: 0},
					Factor:    aletheia.Rational{Numerator: 1, Denominator: 10}, Offset: aletheia.Rational{Numerator: -40, Denominator: 1}, Minimum: aletheia.Rational{Numerator: -40, Denominator: 1}, Maximum: aletheia.Rational{Numerator: 215, Denominator: 1}, Unit: "degC",
				},
			},
		}},
	}
	err = c.ParseDBC(dbc)
	if err != nil {
		t.Fatalf("ParseDBC with mux: %v", err)
	}
}

func TestFormatDBC_ExtendedID(t *testing.T) {
	mock := aletheia.NewMockBackend(
		aletheia.Respond(`{
			"status":"success",
			"dbc":{
				"version":"",
				"messages":[{
					"id":419361024,"extended":true,"name":"J1939Msg","dlc":8,"sender":"Node",
					"signals":[]
				}]
			}
		}`),
	)
	c, err := aletheia.NewClient(mock)
	if err != nil {
		t.Fatal(err)
	}
	defer c.Close()

	dbc, err := c.FormatDBC()
	if err != nil {
		t.Fatalf("FormatDBC: %v", err)
	}
	if len(dbc.Messages) != 1 {
		t.Fatalf("expected 1 message, got %d", len(dbc.Messages))
	}
	if !dbc.Messages[0].ID.IsExtended() {
		t.Error("expected extended ID")
	}
	if dbc.Messages[0].ID.Value() != 419361024 {
		t.Errorf("expected 419361024, got %d", dbc.Messages[0].ID.Value())
	}
}

func TestFormatDBC_Multiplexed(t *testing.T) {
	mock := aletheia.NewMockBackend(
		aletheia.Respond(`{
			"status":"success",
			"dbc":{
				"version":"",
				"messages":[{
					"id":512,"extended":false,"name":"MuxMsg","dlc":8,"sender":"ECU",
					"signals":[{
						"name":"MuxSel","startBit":0,"length":8,"byteOrder":"little_endian",
						"signed":false,"factor":1,"offset":0,"minimum":0,"maximum":3,"unit":""
					},{
						"name":"TempA","startBit":8,"length":16,"byteOrder":"little_endian",
						"signed":false,"factor":{"numerator":1,"denominator":10},"offset":-40,"minimum":-40,"maximum":215,"unit":"degC",
						"multiplexor":"MuxSel","multiplex_value":0
					}]
				}]
			}
		}`),
	)
	c, err := aletheia.NewClient(mock)
	if err != nil {
		t.Fatal(err)
	}
	defer c.Close()

	dbc, err := c.FormatDBC()
	if err != nil {
		t.Fatalf("FormatDBC: %v", err)
	}
	sigs := dbc.Messages[0].Signals
	if len(sigs) != 2 {
		t.Fatalf("expected 2 signals, got %d", len(sigs))
	}
	if _, ok := sigs[0].Presence.(aletheia.AlwaysPresent); !ok {
		t.Errorf("MuxSel expected AlwaysPresent, got %T", sigs[0].Presence)
	}
	mux, ok := sigs[1].Presence.(aletheia.Multiplexed)
	if !ok {
		t.Fatalf("TempA expected Multiplexed, got %T", sigs[1].Presence)
	}
	if mux.Multiplexor != "MuxSel" {
		t.Errorf("expected multiplexor MuxSel, got %s", mux.Multiplexor)
	}
	if mux.MuxValue != 0 {
		t.Errorf("expected mux value 0, got %d", mux.MuxValue)
	}
}

func TestExtractSignals_Errors(t *testing.T) {
	mock := aletheia.NewMockBackend(
		aletheia.Respond(`{
			"status":"success",
			"values":[],
			"errors":[{"name":"Broken","error":"bit extraction failed"}],
			"absent":[]
		}`),
	)
	c, err := aletheia.NewClient(mock)
	if err != nil {
		t.Fatal(err)
	}
	defer c.Close()

	sid, _ := aletheia.NewStandardID(0x123)
	data := aletheia.FramePayload{0, 0, 0, 0, 0, 0, 0, 0}
	result, err := c.ExtractSignals(sid, dlc8(), data)
	if err != nil {
		t.Fatalf("ExtractSignals: %v", err)
	}
	if len(result.Errors) != 1 {
		t.Fatalf("expected 1 error, got %d", len(result.Errors))
	}
	if result.Errors[0].Name != "Broken" {
		t.Errorf("expected Broken, got %s", result.Errors[0].Name)
	}
	if result.Errors[0].Error != "bit extraction failed" {
		t.Errorf("expected 'bit extraction failed', got %q", result.Errors[0].Error)
	}
}

func TestChangedByPredicate(t *testing.T) {
	mock := aletheia.NewMockBackend(
		aletheia.Respond(`{"status":"success"}`),
	)
	c, err := aletheia.NewClient(mock)
	if err != nil {
		t.Fatal(err)
	}
	defer c.Close()

	err = c.SetProperties([]aletheia.Formula{
		aletheia.Atomic{Predicate: aletheia.ChangedBy{Signal: "RPM", Delta: 500}},
	})
	if err != nil {
		t.Fatalf("SetProperties: %v", err)
	}
	// Verify "delta" appears in the serialized JSON.
	if len(mock.Inputs) != 1 {
		t.Fatalf("expected 1 input, got %d", len(mock.Inputs))
	}
	input := mock.Inputs[0]
	if !strings.Contains(input, `"delta"`) {
		t.Errorf("expected delta field in JSON, got: %s", input)
	}
	if !strings.Contains(input, `"changedBy"`) {
		t.Errorf("expected changedBy predicate in JSON, got: %s", input)
	}
}

func TestBetweenPredicate(t *testing.T) {
	mock := aletheia.NewMockBackend(
		aletheia.Respond(`{"status":"success"}`),
	)
	c, err := aletheia.NewClient(mock)
	if err != nil {
		t.Fatal(err)
	}
	defer c.Close()

	err = c.SetProperties([]aletheia.Formula{
		aletheia.Atomic{Predicate: aletheia.Between{Signal: "Temp", Min: -40, Max: 120}},
	})
	if err != nil {
		t.Fatalf("SetProperties: %v", err)
	}
	if len(mock.Inputs) != 1 {
		t.Fatalf("expected 1 input, got %d", len(mock.Inputs))
	}
	input := mock.Inputs[0]
	if !strings.Contains(input, `"between"`) {
		t.Errorf("expected between predicate in JSON, got: %s", input)
	}
	if !strings.Contains(input, `"min"`) || !strings.Contains(input, `"max"`) {
		t.Errorf("expected min/max fields in JSON, got: %s", input)
	}
}

func TestZeroDenominatorRational(t *testing.T) {
	mock := aletheia.NewMockBackend(
		aletheia.Respond(`{
			"status":"success",
			"values":[{"name":"Bad","value":{"numerator":1,"denominator":0}}],
			"errors":[],
			"absent":[]
		}`),
	)
	c, err := aletheia.NewClient(mock)
	if err != nil {
		t.Fatal(err)
	}
	defer c.Close()

	sid, _ := aletheia.NewStandardID(0x100)
	_, err = c.ExtractSignals(sid, dlc8(), aletheia.FramePayload{})
	if err == nil {
		t.Fatal("expected error for zero denominator")
	}
}

func TestBuildFrame_ByteOutOfRange(t *testing.T) {
	mock := aletheia.NewMockBackend(
		aletheia.Respond(`{"status":"success"}`),
		aletheia.Respond(`{"status":"success","data":[256,0,0,0,0,0,0,0]}`),
	)
	c, err := aletheia.NewClient(mock)
	if err != nil {
		t.Fatal(err)
	}
	defer c.Close()

	if err := c.ParseDBC(testDBC()); err != nil {
		t.Fatal(err)
	}
	sid, _ := aletheia.NewStandardID(0x123)
	dlc, _ := aletheia.NewDLC(8)
	_, err = c.BuildFrame(sid, []aletheia.SignalValue{{Name: "Speed", Value: 100}}, dlc)
	if err == nil {
		t.Fatal("expected error for byte value 256")
	}
	if !strings.Contains(err.Error(), "out of range") {
		t.Errorf("expected 'out of range' in error, got: %s", err)
	}
}

func TestBuildFrame_VariableLengthPayload(t *testing.T) {
	mock := aletheia.NewMockBackend(
		aletheia.Respond(`{"status":"success"}`),
		aletheia.Respond(`{"status":"success","data":[1,2,3,4,5,6,7]}`),
	)
	c, err := aletheia.NewClient(mock)
	if err != nil {
		t.Fatal(err)
	}
	defer c.Close()

	if err := c.ParseDBC(testDBC()); err != nil {
		t.Fatal(err)
	}
	sid, _ := aletheia.NewStandardID(0x123)
	dlc, _ := aletheia.NewDLC(8)
	payload, err := c.BuildFrame(sid, []aletheia.SignalValue{{Name: "Speed", Value: 100}}, dlc)
	if err != nil {
		t.Fatalf("BuildFrame: %v", err)
	}
	if !bytes.Equal(payload, aletheia.FramePayload{1, 2, 3, 4, 5, 6, 7}) {
		t.Errorf("unexpected payload: %v", payload)
	}
}

func TestExtractSignals_InvalidStatus(t *testing.T) {
	mock := aletheia.NewMockBackend(
		aletheia.Respond(`{"status":"success"}`),
		aletheia.Respond(`{"status":"validation","values":[],"errors":[],"absent":[]}`),
	)
	c, err := aletheia.NewClient(mock)
	if err != nil {
		t.Fatal(err)
	}
	defer c.Close()

	if err := c.ParseDBC(testDBC()); err != nil {
		t.Fatal(err)
	}
	sid, _ := aletheia.NewStandardID(0x123)
	data := aletheia.FramePayload{0, 0, 0, 0, 0, 0, 0, 0}
	_, err = c.ExtractSignals(sid, dlc8(), data)
	if err == nil {
		t.Fatal("expected error for unexpected status 'validation'")
	}
	if !strings.Contains(err.Error(), "expected success") {
		t.Errorf("expected 'expected success' in error, got: %s", err)
	}
}

func TestExtractSignals_NonStringAbsent(t *testing.T) {
	mock := aletheia.NewMockBackend(
		aletheia.Respond(`{"status":"success"}`),
		aletheia.Respond(`{"status":"success","values":[],"errors":[],"absent":[123]}`),
	)
	c, err := aletheia.NewClient(mock)
	if err != nil {
		t.Fatal(err)
	}
	defer c.Close()

	if err := c.ParseDBC(testDBC()); err != nil {
		t.Fatal(err)
	}
	sid, _ := aletheia.NewStandardID(0x123)
	data := aletheia.FramePayload{0, 0, 0, 0, 0, 0, 0, 0}
	_, err = c.ExtractSignals(sid, dlc8(), data)
	if err == nil {
		t.Fatal("expected error for non-string in absent array")
	}
	if !strings.Contains(err.Error(), "expected string in absent") {
		t.Errorf("expected 'expected string in absent' in error, got: %s", err)
	}
}

// --- Group P: Malformed response tests ---

func TestFormatDBC_InvalidByteOrder(t *testing.T) {
	mock := aletheia.NewMockBackend(
		aletheia.Respond(`{
			"status":"success",
			"dbc":{
				"version":"",
				"messages":[{
					"id":100,"extended":false,"name":"Msg","dlc":8,"sender":"ECU",
					"signals":[{
						"name":"Sig","startBit":0,"length":8,"byteOrder":"middle_endian",
						"signed":false,"factor":1,"offset":0,"minimum":0,"maximum":255,"unit":""
					}]
				}]
			}
		}`),
	)
	c, err := aletheia.NewClient(mock)
	if err != nil {
		t.Fatal(err)
	}
	defer c.Close()

	_, err = c.FormatDBC()
	if err == nil {
		t.Fatal("expected error for invalid byteOrder")
	}
	aErr, ok := err.(*aletheia.Error)
	if !ok {
		t.Fatalf("expected *aletheia.Error, got %T", err)
	}
	if aErr.Kind != aletheia.ErrProtocol {
		t.Errorf("expected ErrProtocol, got %s", aErr.Kind)
	}
}

func TestFormatDBC_NegativeID(t *testing.T) {
	mock := aletheia.NewMockBackend(
		aletheia.Respond(`{
			"status":"success",
			"dbc":{
				"version":"",
				"messages":[{
					"id":-1,"extended":false,"name":"Msg","dlc":8,"sender":"ECU",
					"signals":[]
				}]
			}
		}`),
	)
	c, err := aletheia.NewClient(mock)
	if err != nil {
		t.Fatal(err)
	}
	defer c.Close()

	_, err = c.FormatDBC()
	if err == nil {
		t.Fatal("expected error for negative ID")
	}
	aErr, ok := err.(*aletheia.Error)
	if !ok {
		t.Fatalf("expected *aletheia.Error, got %T", err)
	}
	if aErr.Kind != aletheia.ErrProtocol {
		t.Errorf("expected ErrProtocol, got %s", aErr.Kind)
	}
}

func TestFormatDBC_MissingSignalName(t *testing.T) {
	mock := aletheia.NewMockBackend(
		aletheia.Respond(`{
			"status":"success",
			"dbc":{
				"version":"",
				"messages":[{
					"id":100,"extended":false,"name":"Msg","dlc":8,"sender":"ECU",
					"signals":[{
						"startBit":0,"length":8,"byteOrder":"little_endian",
						"signed":false,"factor":1,"offset":0,"minimum":0,"maximum":255,"unit":""
					}]
				}]
			}
		}`),
	)
	c, err := aletheia.NewClient(mock)
	if err != nil {
		t.Fatal(err)
	}
	defer c.Close()

	_, err = c.FormatDBC()
	if err == nil {
		t.Fatal("expected error for missing signal name")
	}
	aErr, ok := err.(*aletheia.Error)
	if !ok {
		t.Fatalf("expected *aletheia.Error, got %T", err)
	}
	if aErr.Kind != aletheia.ErrProtocol {
		t.Errorf("expected ErrProtocol, got %s", aErr.Kind)
	}
}

func TestBetween_MinExceedsMax(t *testing.T) {
	mock := aletheia.NewMockBackend()
	c, err := aletheia.NewClient(mock)
	if err != nil {
		t.Fatal(err)
	}
	defer c.Close()

	err = c.SetProperties([]aletheia.Formula{
		aletheia.Atomic{Predicate: aletheia.Between{Signal: "Temp", Min: 100, Max: 50}},
	})
	if err == nil {
		t.Fatal("expected error for Between with Min > Max")
	}
	aErr, ok := err.(*aletheia.Error)
	if !ok {
		t.Fatalf("expected *aletheia.Error, got %T", err)
	}
	if aErr.Kind != aletheia.ErrValidation {
		t.Errorf("expected ErrValidation, got %s", aErr.Kind)
	}
}

// --- Group R6-J: startBit/length range validation tests ---

func TestFormatDBC_StartBitOutOfRange(t *testing.T) {
	mock := aletheia.NewMockBackend(
		aletheia.Respond(`{
			"status":"success",
			"dbc":{
				"version":"",
				"messages":[{
					"id":100,"extended":false,"name":"Msg","dlc":8,"sender":"ECU",
					"signals":[{
						"name":"Sig","startBit":600,"length":8,"byteOrder":"little_endian",
						"signed":false,"factor":1,"offset":0,"minimum":0,"maximum":255,"unit":""
					}]
				}]
			}
		}`),
	)
	c, err := aletheia.NewClient(mock)
	if err != nil {
		t.Fatal(err)
	}
	defer c.Close()

	_, err = c.FormatDBC()
	if err == nil {
		t.Fatal("expected error for startBit=600")
	}
	aErr, ok := err.(*aletheia.Error)
	if !ok {
		t.Fatalf("expected *aletheia.Error, got %T", err)
	}
	if aErr.Kind != aletheia.ErrProtocol {
		t.Errorf("expected ErrProtocol, got %s", aErr.Kind)
	}
	if !strings.Contains(err.Error(), "out of range") {
		t.Errorf("expected 'out of range' in error, got: %s", err)
	}
}

func TestFormatDBC_LengthZero(t *testing.T) {
	mock := aletheia.NewMockBackend(
		aletheia.Respond(`{
			"status":"success",
			"dbc":{
				"version":"",
				"messages":[{
					"id":100,"extended":false,"name":"Msg","dlc":8,"sender":"ECU",
					"signals":[{
						"name":"Sig","startBit":0,"length":0,"byteOrder":"little_endian",
						"signed":false,"factor":1,"offset":0,"minimum":0,"maximum":255,"unit":""
					}]
				}]
			}
		}`),
	)
	c, err := aletheia.NewClient(mock)
	if err != nil {
		t.Fatal(err)
	}
	defer c.Close()

	_, err = c.FormatDBC()
	if err == nil {
		t.Fatal("expected error for length=0")
	}
	aErr, ok := err.(*aletheia.Error)
	if !ok {
		t.Fatalf("expected *aletheia.Error, got %T", err)
	}
	if aErr.Kind != aletheia.ErrProtocol {
		t.Errorf("expected ErrProtocol, got %s", aErr.Kind)
	}
	if !strings.Contains(err.Error(), "out of range") {
		t.Errorf("expected 'out of range' in error, got: %s", err)
	}
}

func TestFormatDBC_LengthExcessive(t *testing.T) {
	mock := aletheia.NewMockBackend(
		aletheia.Respond(`{
			"status":"success",
			"dbc":{
				"version":"",
				"messages":[{
					"id":100,"extended":false,"name":"Msg","dlc":8,"sender":"ECU",
					"signals":[{
						"name":"Sig","startBit":0,"length":65,"byteOrder":"little_endian",
						"signed":false,"factor":1,"offset":0,"minimum":0,"maximum":255,"unit":""
					}]
				}]
			}
		}`),
	)
	c, err := aletheia.NewClient(mock)
	if err != nil {
		t.Fatal(err)
	}
	defer c.Close()

	_, err = c.FormatDBC()
	if err == nil {
		t.Fatal("expected error for length=65")
	}
	aErr, ok := err.(*aletheia.Error)
	if !ok {
		t.Fatalf("expected *aletheia.Error, got %T", err)
	}
	if aErr.Kind != aletheia.ErrProtocol {
		t.Errorf("expected ErrProtocol, got %s", aErr.Kind)
	}
	if !strings.Contains(err.Error(), "out of range") {
		t.Errorf("expected 'out of range' in error, got: %s", err)
	}
}

// --- Group R6-K: Empty name validation tests ---

func TestExtractSignals_EmptySignalName(t *testing.T) {
	mock := aletheia.NewMockBackend(
		aletheia.Respond(`{
			"status":"success",
			"values":[{"name":"","value":42}],
			"errors":[],
			"absent":[]
		}`),
	)
	c, err := aletheia.NewClient(mock)
	if err != nil {
		t.Fatal(err)
	}
	defer c.Close()

	sid, _ := aletheia.NewStandardID(0x100)
	data := aletheia.FramePayload{0, 0, 0, 0, 0, 0, 0, 0}
	_, err = c.ExtractSignals(sid, dlc8(), data)
	if err == nil {
		t.Fatal("expected error for empty signal name in extraction")
	}
	aErr, ok := err.(*aletheia.Error)
	if !ok {
		t.Fatalf("expected *aletheia.Error, got %T", err)
	}
	if aErr.Kind != aletheia.ErrProtocol {
		t.Errorf("expected ErrProtocol, got %s", aErr.Kind)
	}
}

func TestFormatDBC_EmptyMessageName(t *testing.T) {
	mock := aletheia.NewMockBackend(
		aletheia.Respond(`{
			"status":"success",
			"dbc":{
				"version":"",
				"messages":[{
					"id":100,"extended":false,"name":"","dlc":8,"sender":"ECU",
					"signals":[]
				}]
			}
		}`),
	)
	c, err := aletheia.NewClient(mock)
	if err != nil {
		t.Fatal(err)
	}
	defer c.Close()

	_, err = c.FormatDBC()
	if err == nil {
		t.Fatal("expected error for empty message name")
	}
	aErr, ok := err.(*aletheia.Error)
	if !ok {
		t.Fatalf("expected *aletheia.Error, got %T", err)
	}
	if aErr.Kind != aletheia.ErrProtocol {
		t.Errorf("expected ErrProtocol, got %s", aErr.Kind)
	}
}
