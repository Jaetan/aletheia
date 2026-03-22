package aletheia_test

import (
	"strings"
	"sync"
	"testing"

	"github.com/aletheia-automotive/aletheia-go/aletheia"
)

// --- Helper: minimal DBC for testing ---

func testDBC() aletheia.DbcDefinition {
	sid, _ := aletheia.NewStandardID(0x123)
	dlc, _ := aletheia.NewDLC(8)
	return aletheia.DbcDefinition{
		Version: "1.0",
		Messages: []aletheia.DbcMessage{
			{
				ID:     sid,
				Name:   "EngineData",
				DLC:    dlc,
				Sender: "ECU",
				Signals: []aletheia.DbcSignal{
					{
						Name:      "Speed",
						StartBit:  0,
						BitLength: 16,
						ByteOrder: aletheia.LittleEndian,
						IsSigned:  false,
						Factor:    0.1,
						Offset:    0,
						Minimum:   0,
						Maximum:   300,
						Unit:      "km/h",
						Presence:  aletheia.AlwaysPresent{},
					},
				},
			},
		},
	}
}

// --- DBC operations ---

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
						"signed":false,"factor":0.1,"offset":0,"minimum":0,"maximum":300,"unit":"km/h"
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

// --- Signal operations ---

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
	result, err := c.ExtractSignals(sid, aletheia.FramePayload{0xDE, 0xAD, 0xBE, 0xEF, 0, 0, 0, 0})
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
	result, err := c.ExtractSignals(sid, aletheia.FramePayload{})
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

	sid, _ := aletheia.NewStandardID(0x123)
	payload, err := c.BuildFrame(sid, []aletheia.SignalValue{
		{Name: "Speed", Value: 120.5},
	})
	if err != nil {
		t.Fatalf("BuildFrame: %v", err)
	}
	expected := aletheia.FramePayload{0xDE, 0xAD, 0xBE, 0xEF, 0, 0, 0, 0}
	if *payload != expected {
		t.Errorf("expected %v, got %v", expected, *payload)
	}
}

func TestUpdateFrame(t *testing.T) {
	mock := aletheia.NewMockBackend(
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

	sid, _ := aletheia.NewStandardID(0x123)
	data := aletheia.FramePayload{0, 0, 0, 0, 0, 0, 0, 0}
	payload, err := c.UpdateFrame(sid, data, []aletheia.SignalValue{
		{Name: "Speed", Value: 100.0},
	})
	if err != nil {
		t.Fatalf("UpdateFrame: %v", err)
	}
	if payload[1] != 100 {
		t.Errorf("expected byte[1]=100, got %d", payload[1])
	}
}

// --- Streaming LTL operations ---

func TestStreamingLTL_NoViolation(t *testing.T) {
	mock := aletheia.NewMockBackend(
		aletheia.Respond(`{"status":"success"}`), // SetProperties
		aletheia.Respond(`{"status":"success"}`), // StartStream
		aletheia.Respond(`{"status":"ack"}`),     // SendFrame
		aletheia.Respond(`{"status":"ack"}`),     // SendFrame
		aletheia.Respond(`{
			"status":"complete",
			"results":[{"property_index":0,"status":"satisfaction"}]
		}`), // EndStream
	)
	c, err := aletheia.NewClient(mock)
	if err != nil {
		t.Fatal(err)
	}
	defer c.Close()

	err = c.SetProperties([]aletheia.Formula{
		aletheia.Always{Inner: aletheia.Atomic{Predicate: aletheia.LessThan{
			Signal: "Speed", Value: 200,
		}}},
	})
	if err != nil {
		t.Fatalf("SetProperties: %v", err)
	}

	err = c.StartStream()
	if err != nil {
		t.Fatalf("StartStream: %v", err)
	}

	sid, _ := aletheia.NewStandardID(0x123)
	data := aletheia.FramePayload{0x64, 0, 0, 0, 0, 0, 0, 0}

	resp1, err := c.SendFrame(aletheia.Timestamp{Microseconds: 1000}, sid, data)
	if err != nil {
		t.Fatalf("SendFrame 1: %v", err)
	}
	if _, ok := resp1.(aletheia.Ack); !ok {
		t.Errorf("expected Ack, got %T", resp1)
	}

	resp2, err := c.SendFrame(aletheia.Timestamp{Microseconds: 2000}, sid, data)
	if err != nil {
		t.Fatalf("SendFrame 2: %v", err)
	}
	if _, ok := resp2.(aletheia.Ack); !ok {
		t.Errorf("expected Ack, got %T", resp2)
	}

	result, err := c.EndStream()
	if err != nil {
		t.Fatalf("EndStream: %v", err)
	}
	if len(result.Results) != 1 {
		t.Fatalf("expected 1 result, got %d", len(result.Results))
	}
	if result.Results[0].Verdict != aletheia.Holds {
		t.Errorf("expected Holds, got %s", result.Results[0].Verdict)
	}
}

func TestStreamingLTL_Violation(t *testing.T) {
	mock := aletheia.NewMockBackend(
		aletheia.Respond(`{"status":"success"}`), // SetProperties
		aletheia.Respond(`{"status":"success"}`), // StartStream
		aletheia.Respond(`{
			"status":"violation",
			"property_index":0,
			"timestamp":5000,
			"reason":"Speed >= 200"
		}`), // SendFrame — violation
		aletheia.Respond(`{
			"status":"complete",
			"results":[{"property_index":0,"status":"violation","timestamp":5000,"reason":"Speed >= 200"}]
		}`), // EndStream
	)
	c, err := aletheia.NewClient(mock)
	if err != nil {
		t.Fatal(err)
	}
	defer c.Close()

	err = c.SetProperties([]aletheia.Formula{
		aletheia.Never(aletheia.GreaterThanOrEqual{Signal: "Speed", Value: 200}),
	})
	if err != nil {
		t.Fatalf("SetProperties: %v", err)
	}

	err = c.StartStream()
	if err != nil {
		t.Fatalf("StartStream: %v", err)
	}

	sid, _ := aletheia.NewStandardID(0x123)
	data := aletheia.FramePayload{0xFF, 0xFF, 0, 0, 0, 0, 0, 0}

	resp, err := c.SendFrame(aletheia.Timestamp{Microseconds: 5000}, sid, data)
	if err != nil {
		t.Fatalf("SendFrame: %v", err)
	}
	v, ok := resp.(aletheia.Violation)
	if !ok {
		t.Fatalf("expected Violation, got %T", resp)
	}
	if v.PropertyIndex != 0 {
		t.Errorf("expected property 0, got %d", v.PropertyIndex)
	}
	if v.Timestamp.Microseconds != 5000 {
		t.Errorf("expected ts=5000, got %d", v.Timestamp.Microseconds)
	}
	if v.Reason != "Speed >= 200" {
		t.Errorf("expected reason 'Speed >= 200', got %q", v.Reason)
	}

	result, err := c.EndStream()
	if err != nil {
		t.Fatalf("EndStream: %v", err)
	}
	if result.Results[0].Verdict != aletheia.Fails {
		t.Errorf("expected Fails, got %s", result.Results[0].Verdict)
	}
	if result.Results[0].Timestamp == nil {
		t.Fatal("expected non-nil timestamp")
	}
	if result.Results[0].Timestamp.Microseconds != 5000 {
		t.Errorf("expected ts=5000, got %d", result.Results[0].Timestamp.Microseconds)
	}
}

// --- Error handling ---

func TestErrorResponse(t *testing.T) {
	mock := aletheia.NewMockBackend(
		aletheia.Respond(`{"status":"error","message":"no DBC loaded"}`),
	)
	c, err := aletheia.NewClient(mock)
	if err != nil {
		t.Fatal(err)
	}
	defer c.Close()

	_, err = c.FormatDBC()
	if err == nil {
		t.Fatal("expected error")
	}
	aErr, ok := err.(*aletheia.Error)
	if !ok {
		t.Fatalf("expected *aletheia.Error, got %T", err)
	}
	if aErr.Kind != aletheia.ErrProtocol {
		t.Errorf("expected ErrProtocol, got %s", aErr.Kind)
	}
}

func TestBackendError(t *testing.T) {
	mock := aletheia.NewMockBackend(
		aletheia.RespondErr(aletheia.NewMockError("connection lost")),
	)
	c, err := aletheia.NewClient(mock)
	if err != nil {
		t.Fatal(err)
	}
	defer c.Close()

	err = c.ParseDBC(testDBC())
	if err == nil {
		t.Fatal("expected error from backend")
	}
}

// --- Type validation ---

func TestStandardID_Range(t *testing.T) {
	_, err := aletheia.NewStandardID(2048)
	if err == nil {
		t.Error("expected error for standard ID > 2047")
	}

	sid, err := aletheia.NewStandardID(2047)
	if err != nil {
		t.Fatalf("expected success for 2047: %v", err)
	}
	if sid.Value() != 2047 {
		t.Errorf("expected 2047, got %d", sid.Value())
	}
	if sid.IsExtended() {
		t.Error("standard ID should not be extended")
	}
}

func TestExtendedID_Range(t *testing.T) {
	_, err := aletheia.NewExtendedID(536870912)
	if err == nil {
		t.Error("expected error for extended ID > 536870911")
	}

	eid, err := aletheia.NewExtendedID(536870911)
	if err != nil {
		t.Fatalf("expected success for 536870911: %v", err)
	}
	if eid.Value() != 536870911 {
		t.Errorf("expected 536870911, got %d", eid.Value())
	}
	if !eid.IsExtended() {
		t.Error("extended ID should be extended")
	}
}

func TestDLC_Range(t *testing.T) {
	_, err := aletheia.NewDLC(9)
	if err == nil {
		t.Error("expected error for DLC > 8")
	}

	dlc, err := aletheia.NewDLC(8)
	if err != nil {
		t.Fatalf("expected success for 8: %v", err)
	}
	if dlc.Value() != 8 {
		t.Errorf("expected 8, got %d", dlc.Value())
	}
}

func TestTimestamp_Duration(t *testing.T) {
	ts := aletheia.Timestamp{Microseconds: 1_000_000}
	if ts.Duration().Seconds() != 1.0 {
		t.Errorf("expected 1s, got %v", ts.Duration())
	}
}

// --- Metric formulas ---

func TestMetricFormulas(t *testing.T) {
	mock := aletheia.NewMockBackend(
		aletheia.Respond(`{"status":"success"}`),
	)
	c, err := aletheia.NewClient(mock)
	if err != nil {
		t.Fatal(err)
	}
	defer c.Close()

	err = c.SetProperties([]aletheia.Formula{
		aletheia.AlwaysWithin(
			aletheia.Timestamp{Microseconds: 5_000_000},
			aletheia.Atomic{Predicate: aletheia.LessThan{Signal: "Speed", Value: 200}},
		),
		aletheia.EventuallyWithin(
			aletheia.Timestamp{Microseconds: 1_000_000},
			aletheia.Atomic{Predicate: aletheia.Equals{Signal: "Mode", Value: 1}},
		),
	})
	if err != nil {
		t.Fatalf("SetProperties: %v", err)
	}
}

// --- Extended ID in DBC ---

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

// --- Multiplexed signals ---

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
					Factor: 1, Offset: 0, Minimum: 0, Maximum: 3, Unit: "",
				},
				{
					Name: "TempA", StartBit: 8, BitLength: 16,
					ByteOrder: aletheia.LittleEndian,
					Presence:  aletheia.Multiplexed{Multiplexor: "MuxSelector", MuxValue: 0},
					Factor:    0.1, Offset: -40, Minimum: -40, Maximum: 215, Unit: "degC",
				},
			},
		}},
	}
	err = c.ParseDBC(dbc)
	if err != nil {
		t.Fatalf("ParseDBC with mux: %v", err)
	}
}

// --- Verdict String ---

func TestVerdictString(t *testing.T) {
	if aletheia.Holds.String() != "holds" {
		t.Errorf("expected 'holds', got %q", aletheia.Holds.String())
	}
	if aletheia.Fails.String() != "fails" {
		t.Errorf("expected 'fails', got %q", aletheia.Fails.String())
	}
}

// --- MockBackend exhaustion ---

func TestMockBackendExhaustion(t *testing.T) {
	mock := aletheia.NewMockBackend() // no responses
	c, err := aletheia.NewClient(mock)
	if err != nil {
		t.Fatal(err)
	}
	defer c.Close()

	err = c.ParseDBC(testDBC())
	if err == nil {
		t.Fatal("expected error when mock exhausted")
	}
}

// --- Use-after-Close ---

func TestUseAfterClose(t *testing.T) {
	mock := aletheia.NewMockBackend(
		aletheia.Respond(`{"status":"success"}`),
	)
	c, err := aletheia.NewClient(mock)
	if err != nil {
		t.Fatal(err)
	}
	c.Close()

	// Calling after Close should return a state error, not crash.
	err = c.ParseDBC(testDBC())
	if err == nil {
		t.Fatal("expected error after Close")
	}
	aErr, ok := err.(*aletheia.Error)
	if !ok {
		t.Fatalf("expected *aletheia.Error, got %T", err)
	}
	if aErr.Kind != aletheia.ErrState {
		t.Errorf("expected ErrState, got %s", aErr.Kind)
	}

	// Double-close should be safe.
	c.Close()
}

// --- FormatDBC with extended CAN ID ---

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

// --- FormatDBC with multiplexed signal ---

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
						"signed":false,"factor":0.1,"offset":-40,"minimum":-40,"maximum":215,"unit":"degC",
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

// --- Signal extraction errors ---

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
	result, err := c.ExtractSignals(sid, aletheia.FramePayload{})
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

// --- ChangedBy predicate serialization ---

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

// --- Between predicate serialization ---

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

// --- Zero denominator rational ---

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
	_, err = c.ExtractSignals(sid, aletheia.FramePayload{})
	if err == nil {
		t.Fatal("expected error for zero denominator")
	}
}

// --- Constructor error type ---

func TestConstructorErrorType(t *testing.T) {
	_, err := aletheia.NewStandardID(2048)
	if err == nil {
		t.Fatal("expected error")
	}
	aErr, ok := err.(*aletheia.Error)
	if !ok {
		t.Fatalf("expected *aletheia.Error, got %T", err)
	}
	if aErr.Kind != aletheia.ErrValidation {
		t.Errorf("expected ErrValidation, got %s", aErr.Kind)
	}
}

// --- Round 2 edge case tests ---

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

	c.ParseDBC(testDBC())
	sid, _ := aletheia.NewStandardID(0x123)
	_, err = c.BuildFrame(sid, []aletheia.SignalValue{{Name: "Speed", Value: 100}})
	if err == nil {
		t.Fatal("expected error for byte value 256")
	}
	if !strings.Contains(err.Error(), "out of range") {
		t.Errorf("expected 'out of range' in error, got: %s", err)
	}
}

func TestBuildFrame_InvalidByteCount(t *testing.T) {
	mock := aletheia.NewMockBackend(
		aletheia.Respond(`{"status":"success"}`),
		aletheia.Respond(`{"status":"success","data":[1,2,3,4,5,6,7]}`),
	)
	c, err := aletheia.NewClient(mock)
	if err != nil {
		t.Fatal(err)
	}
	defer c.Close()

	c.ParseDBC(testDBC())
	sid, _ := aletheia.NewStandardID(0x123)
	_, err = c.BuildFrame(sid, []aletheia.SignalValue{{Name: "Speed", Value: 100}})
	if err == nil {
		t.Fatal("expected error for 7-byte frame")
	}
	if !strings.Contains(err.Error(), "8-byte") {
		t.Errorf("expected '8-byte' in error, got: %s", err)
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

	c.ParseDBC(testDBC())
	sid, _ := aletheia.NewStandardID(0x123)
	_, err = c.ExtractSignals(sid, aletheia.FramePayload{})
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

	c.ParseDBC(testDBC())
	sid, _ := aletheia.NewStandardID(0x123)
	_, err = c.ExtractSignals(sid, aletheia.FramePayload{})
	if err == nil {
		t.Fatal("expected error for non-string in absent array")
	}
	if !strings.Contains(err.Error(), "expected string in absent") {
		t.Errorf("expected 'expected string in absent' in error, got: %s", err)
	}
}

func TestEndStream_TimestampParseError(t *testing.T) {
	mock := aletheia.NewMockBackend(
		aletheia.Respond(`{"status":"success"}`),
		aletheia.Respond(`{"status":"success"}`),
		aletheia.Respond(`{
			"status":"complete",
			"results":[{
				"property_index":0,
				"status":"satisfaction",
				"reason":"",
				"timestamp":"not_a_number"
			}]
		}`),
	)
	c, err := aletheia.NewClient(mock)
	if err != nil {
		t.Fatal(err)
	}
	defer c.Close()

	c.SetProperties([]aletheia.Formula{
		aletheia.Always{Inner: aletheia.Atomic{Predicate: aletheia.LessThan{Signal: "Speed", Value: 300}}},
	})
	c.StartStream()

	_, err = c.EndStream()
	if err == nil {
		t.Fatal("expected error for non-numeric timestamp")
	}
	if !strings.Contains(err.Error(), "invalid timestamp") {
		t.Errorf("expected 'invalid timestamp' in error, got: %s", err)
	}
}

func TestConcurrentSendFrame(t *testing.T) {
	const n = 10
	responses := make([]aletheia.MockResponse, 0, n+2)
	responses = append(responses, aletheia.Respond(`{"status":"success"}`)) // SetProperties
	responses = append(responses, aletheia.Respond(`{"status":"success"}`)) // StartStream
	for i := 0; i < n; i++ {
		responses = append(responses, aletheia.Respond(`{"status":"ack"}`))
	}

	mock := aletheia.NewMockBackend(responses...)
	c, err := aletheia.NewClient(mock)
	if err != nil {
		t.Fatal(err)
	}
	defer c.Close()

	c.SetProperties([]aletheia.Formula{
		aletheia.Always{Inner: aletheia.Atomic{Predicate: aletheia.LessThan{Signal: "Speed", Value: 300}}},
	})
	c.StartStream()

	var wg sync.WaitGroup
	for i := 0; i < n; i++ {
		wg.Add(1)
		go func(idx int) {
			defer wg.Done()
			sid, _ := aletheia.NewStandardID(uint16(0x100 + idx))
			data := aletheia.FramePayload{byte(idx), 0, 0, 0, 0, 0, 0, 0}
			_, _ = c.SendFrame(aletheia.Timestamp{Microseconds: int64(idx * 1000)}, sid, data)
		}(i)
	}
	wg.Wait()
}
