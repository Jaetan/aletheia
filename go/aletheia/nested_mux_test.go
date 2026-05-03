package aletheia_test

import (
	"testing"

	"github.com/aletheia-automotive/aletheia-go/aletheia"
)

// nestedMuxDBC returns a 3-level nested multiplexed DBC for testing.
//
//	Mode    : always present (8 bits @ 0)
//	SubMode : present when Mode == 3 (8 bits @ 8)
//	Detail  : present when SubMode == 7 (16 bits @ 16)
//
// Detail is reachable only when Mode == 3 AND SubMode == 7.
func nestedMuxDBC() aletheia.DbcDefinition {
	sid, _ := aletheia.NewStandardID(0x300)
	dlc, _ := aletheia.NewDLC(8)
	return aletheia.DbcDefinition{
		Version: "1.0",
		Messages: []aletheia.DbcMessage{
			{
				ID: sid, Name: "NestedMuxMessage", DLC: dlc, Sender: "ECU",
				Signals: []aletheia.DbcSignal{
					{
						Name: "Mode", StartBit: 0, BitLength: 8,
						ByteOrder: aletheia.LittleEndian, IsSigned: false,
						Factor:  aletheia.Rational{Numerator: 1, Denominator: 1},
						Offset:  aletheia.Rational{Numerator: 0, Denominator: 1},
						Minimum: aletheia.Rational{Numerator: 0, Denominator: 1},
						Maximum: aletheia.Rational{Numerator: 255, Denominator: 1},
						Unit:    "", Presence: aletheia.AlwaysPresent{},
					},
					{
						Name: "SubMode", StartBit: 8, BitLength: 8,
						ByteOrder: aletheia.LittleEndian, IsSigned: false,
						Factor:  aletheia.Rational{Numerator: 1, Denominator: 1},
						Offset:  aletheia.Rational{Numerator: 0, Denominator: 1},
						Minimum: aletheia.Rational{Numerator: 0, Denominator: 1},
						Maximum: aletheia.Rational{Numerator: 255, Denominator: 1},
						Unit:    "",
						Presence: aletheia.Multiplexed{
							Multiplexor: "Mode",
							MuxValues:   []aletheia.MultiplexValue{3},
						},
					},
					{
						Name: "Detail", StartBit: 16, BitLength: 16,
						ByteOrder: aletheia.LittleEndian, IsSigned: false,
						Factor:  aletheia.Rational{Numerator: 1, Denominator: 1},
						Offset:  aletheia.Rational{Numerator: 0, Denominator: 1},
						Minimum: aletheia.Rational{Numerator: 0, Denominator: 1},
						Maximum: aletheia.Rational{Numerator: 65535, Denominator: 1},
						Unit:    "",
						Presence: aletheia.Multiplexed{
							Multiplexor: "SubMode",
							MuxValues:   []aletheia.MultiplexValue{7},
						},
					},
				},
			},
		},
	}
}

// TestNestedMux_ParseDBCAccepted verifies that a 3-level nested multiplexed
// DBC is accepted by ParseDBC. Round-trips through the JSON serializer to
// confirm the chain serializes correctly.
func TestNestedMux_ParseDBCAccepted(t *testing.T) {
	mock := aletheia.NewMockBackend(
		aletheia.RespondParseDBC(nestedMuxDBC()),
	)
	c, err := aletheia.NewClient(mock)
	if err != nil {
		t.Fatal(err)
	}
	defer c.Close()

	if _, err := c.ParseDBC(ctx, nestedMuxDBC()); err != nil {
		t.Fatalf("ParseDBC with nested mux: %v", err)
	}
}

// TestNestedMux_ValidateClean verifies that a well-formed nested mux DBC
// produces no validation errors.
func TestNestedMux_ValidateClean(t *testing.T) {
	mock := aletheia.NewMockBackend(
		aletheia.Respond(`{
			"status":"validation",
			"has_errors":false,
			"issues":[]
		}`),
	)
	c, err := aletheia.NewClient(mock)
	if err != nil {
		t.Fatal(err)
	}
	defer c.Close()

	result, err := c.ValidateDBC(ctx, nestedMuxDBC())
	if err != nil {
		t.Fatalf("ValidateDBC: %v", err)
	}
	if result.HasErrors {
		t.Errorf("expected no errors, got %d issues", len(result.Issues))
	}
}

// TestNestedMux_FullChainMatch_ExtractsLeaf verifies that when every signal
// in the chain matches its multiplexor (Mode=3, SubMode=7), the leaf signal
// (Detail) is successfully extracted.
func TestNestedMux_FullChainMatch_ExtractsLeaf(t *testing.T) {
	mock := aletheia.NewMockBackend(
		aletheia.Respond(`{
			"status":"success",
			"values":[
				{"name":"Mode","value":3},
				{"name":"SubMode","value":7},
				{"name":"Detail","value":43981}
			],
			"errors":[],
			"absent":[]
		}`),
	)
	c, err := aletheia.NewClient(mock)
	if err != nil {
		t.Fatal(err)
	}
	defer c.Close()

	sid, _ := aletheia.NewStandardID(0x300)
	// Mode=3, SubMode=7, Detail=0xABCD (43981)
	data := aletheia.FramePayload{0x03, 0x07, 0xCD, 0xAB, 0, 0, 0, 0}
	result, err := c.ExtractSignals(ctx, sid, dlc8(), data)
	if err != nil {
		t.Fatalf("ExtractSignals: %v", err)
	}
	if len(result.Values) != 3 {
		t.Fatalf("expected 3 values, got %d", len(result.Values))
	}
	if len(result.Absent) != 0 {
		t.Errorf("expected no absent signals, got %v", result.Absent)
	}
	v, ok := result.Get("Detail")
	if !ok {
		t.Fatal("Detail should be present")
	}
	if v != 43981 {
		t.Errorf("Detail = %g, want 43981", v)
	}
}

// TestNestedMux_InnerMismatch_LeafAbsent verifies that when the outer
// multiplexor matches (Mode=3) but the inner one does not (SubMode=5, not 7),
// the leaf signal (Detail) is reported absent.
func TestNestedMux_InnerMismatch_LeafAbsent(t *testing.T) {
	mock := aletheia.NewMockBackend(
		aletheia.Respond(`{
			"status":"success",
			"values":[
				{"name":"Mode","value":3},
				{"name":"SubMode","value":5}
			],
			"errors":[],
			"absent":["Detail"]
		}`),
	)
	c, err := aletheia.NewClient(mock)
	if err != nil {
		t.Fatal(err)
	}
	defer c.Close()

	sid, _ := aletheia.NewStandardID(0x300)
	// Mode=3, SubMode=5 (≠7), Detail bytes ignored
	data := aletheia.FramePayload{0x03, 0x05, 0xCD, 0xAB, 0, 0, 0, 0}
	result, err := c.ExtractSignals(ctx, sid, dlc8(), data)
	if err != nil {
		t.Fatalf("ExtractSignals: %v", err)
	}
	if len(result.Absent) != 1 || result.Absent[0] != "Detail" {
		t.Errorf("expected Absent=[Detail], got %v", result.Absent)
	}
	if _, ok := result.Get("Detail"); ok {
		t.Error("Detail should not be present")
	}
}

// TestNestedMux_OuterMismatch_BothLeavesAbsent verifies that when the outer
// multiplexor does not match (Mode=2, not 3), both the inner mux signal
// (SubMode) and the leaf signal (Detail) are reported absent.
func TestNestedMux_OuterMismatch_BothLeavesAbsent(t *testing.T) {
	mock := aletheia.NewMockBackend(
		aletheia.Respond(`{
			"status":"success",
			"values":[{"name":"Mode","value":2}],
			"errors":[],
			"absent":["SubMode","Detail"]
		}`),
	)
	c, err := aletheia.NewClient(mock)
	if err != nil {
		t.Fatal(err)
	}
	defer c.Close()

	sid, _ := aletheia.NewStandardID(0x300)
	// Mode=2 (≠3), SubMode/Detail bytes ignored
	data := aletheia.FramePayload{0x02, 0x07, 0xCD, 0xAB, 0, 0, 0, 0}
	result, err := c.ExtractSignals(ctx, sid, dlc8(), data)
	if err != nil {
		t.Fatalf("ExtractSignals: %v", err)
	}
	if len(result.Absent) != 2 {
		t.Fatalf("expected 2 absent signals, got %v", result.Absent)
	}
	gotAbsent := map[aletheia.SignalName]bool{}
	for _, n := range result.Absent {
		gotAbsent[n] = true
	}
	if !gotAbsent["SubMode"] || !gotAbsent["Detail"] {
		t.Errorf("expected SubMode and Detail absent, got %v", result.Absent)
	}
}

// TestNestedMux_CycleRejected verifies that the JSON parser correctly
// surfaces a multiplexor_cycle issue from the validator. Two signals A and B
// each multiplex on the other → cycle detected by Aletheia core.
func TestNestedMux_CycleRejected(t *testing.T) {
	mock := aletheia.NewMockBackend(
		aletheia.Respond(`{
			"status":"validation",
			"has_errors":true,
			"issues":[
				{"severity":"error","code":"multiplexor_cycle","detail":"Multiplexor chain for signal A contains a cycle"}
			]
		}`),
	)
	c, err := aletheia.NewClient(mock)
	if err != nil {
		t.Fatal(err)
	}
	defer c.Close()

	// Build a DBC describing the cycle (A muxed by B, B muxed by A); the
	// mock returns a canned cycle error regardless, but the request still
	// has to serialize cleanly.
	sid, _ := aletheia.NewStandardID(0x301)
	dlc, _ := aletheia.NewDLC(8)
	cycleDBC := aletheia.DbcDefinition{
		Version: "1.0",
		Messages: []aletheia.DbcMessage{{
			ID: sid, Name: "CycleMsg", DLC: dlc, Sender: "ECU",
			Signals: []aletheia.DbcSignal{
				{
					Name: "A", StartBit: 0, BitLength: 8,
					ByteOrder: aletheia.LittleEndian, IsSigned: false,
					Factor:  aletheia.Rational{Numerator: 1, Denominator: 1},
					Offset:  aletheia.Rational{Numerator: 0, Denominator: 1},
					Minimum: aletheia.Rational{Numerator: 0, Denominator: 1},
					Maximum: aletheia.Rational{Numerator: 255, Denominator: 1},
					Presence: aletheia.Multiplexed{
						Multiplexor: "B", MuxValues: []aletheia.MultiplexValue{1},
					},
				},
				{
					Name: "B", StartBit: 8, BitLength: 8,
					ByteOrder: aletheia.LittleEndian, IsSigned: false,
					Factor:  aletheia.Rational{Numerator: 1, Denominator: 1},
					Offset:  aletheia.Rational{Numerator: 0, Denominator: 1},
					Minimum: aletheia.Rational{Numerator: 0, Denominator: 1},
					Maximum: aletheia.Rational{Numerator: 255, Denominator: 1},
					Presence: aletheia.Multiplexed{
						Multiplexor: "A", MuxValues: []aletheia.MultiplexValue{1},
					},
				},
			},
		}},
	}

	result, err := c.ValidateDBC(ctx, cycleDBC)
	if err != nil {
		t.Fatalf("ValidateDBC: %v", err)
	}
	if !result.HasErrors {
		t.Fatal("expected has_errors=true")
	}
	if len(result.Issues) != 1 {
		t.Fatalf("expected 1 issue, got %d", len(result.Issues))
	}
	if result.Issues[0].Code != aletheia.IssueMultiplexorCycle {
		t.Errorf("expected multiplexor_cycle, got %s", result.Issues[0].Code)
	}
	if result.Issues[0].Severity != aletheia.SeverityError {
		t.Error("expected error severity")
	}
}
