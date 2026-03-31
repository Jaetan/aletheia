package aletheia_test

import (
	"testing"

	"github.com/aletheia-automotive/aletheia-go/aletheia"
)

// muxDBC returns a DBC with multiplexed signals for testing.
func muxDBC() aletheia.DbcDefinition {
	sid, _ := aletheia.NewStandardID(0x200)
	dlc, _ := aletheia.NewDLC(8)
	return aletheia.DbcDefinition{
		Version: "1.0",
		Messages: []aletheia.DbcMessage{
			{
				ID: sid, Name: "MuxMessage", DLC: dlc, Sender: "ECU",
				Signals: []aletheia.DbcSignal{
					{
						Name: "MuxSelector", StartBit: 0, BitLength: 8,
						ByteOrder: aletheia.LittleEndian, IsSigned: false,
						Factor: aletheia.Rational{Numerator: 1, Denominator: 1}, Offset: aletheia.Rational{Numerator: 0, Denominator: 1}, Minimum: aletheia.Rational{Numerator: 0, Denominator: 1}, Maximum: aletheia.Rational{Numerator: 255, Denominator: 1},
						Unit: "", Presence: aletheia.AlwaysPresent{},
					},
					{
						Name: "Temperature", StartBit: 8, BitLength: 16,
						ByteOrder: aletheia.LittleEndian, IsSigned: true,
						Factor: aletheia.Rational{Numerator: 1, Denominator: 10}, Offset: aletheia.Rational{Numerator: -40, Denominator: 1}, Minimum: aletheia.Rational{Numerator: -40, Denominator: 1}, Maximum: aletheia.Rational{Numerator: 215, Denominator: 1},
						Unit: "degC", Presence: aletheia.Multiplexed{Multiplexor: "MuxSelector", MuxValue: 0},
					},
					{
						Name: "Pressure", StartBit: 8, BitLength: 16,
						ByteOrder: aletheia.LittleEndian, IsSigned: false,
						Factor: aletheia.Rational{Numerator: 1, Denominator: 100}, Offset: aletheia.Rational{Numerator: 0, Denominator: 1}, Minimum: aletheia.Rational{Numerator: 0, Denominator: 1}, Maximum: aletheia.Rational{Numerator: 655, Denominator: 1},
						Unit: "bar", Presence: aletheia.Multiplexed{Multiplexor: "MuxSelector", MuxValue: 1},
					},
					{
						Name: "RPM", StartBit: 24, BitLength: 16,
						ByteOrder: aletheia.LittleEndian, IsSigned: false,
						Factor: aletheia.Rational{Numerator: 1, Denominator: 1}, Offset: aletheia.Rational{Numerator: 0, Denominator: 1}, Minimum: aletheia.Rational{Numerator: 0, Denominator: 1}, Maximum: aletheia.Rational{Numerator: 10000, Denominator: 1},
						Unit: "rpm", Presence: aletheia.Multiplexed{Multiplexor: "MuxSelector", MuxValue: 0},
					},
					{
						Name: "Voltage", StartBit: 40, BitLength: 16,
						ByteOrder: aletheia.LittleEndian, IsSigned: false,
						Factor: aletheia.Rational{Numerator: 1, Denominator: 100}, Offset: aletheia.Rational{Numerator: 0, Denominator: 1}, Minimum: aletheia.Rational{Numerator: 0, Denominator: 1}, Maximum: aletheia.Rational{Numerator: 65, Denominator: 1},
						Unit: "V", Presence: aletheia.AlwaysPresent{},
					},
				},
			},
		},
	}
}

func TestAlwaysPresentSignals(t *testing.T) {
	msg := muxDBC().Messages[0]
	got := msg.AlwaysPresentSignals()
	if len(got) != 2 {
		t.Fatalf("expected 2 always-present signals, got %d", len(got))
	}
	if got[0].Name != "MuxSelector" {
		t.Errorf("got[0].Name = %q, want MuxSelector", got[0].Name)
	}
	if got[1].Name != "Voltage" {
		t.Errorf("got[1].Name = %q, want Voltage", got[1].Name)
	}
}

func TestMultiplexedSignals(t *testing.T) {
	msg := muxDBC().Messages[0]
	got := msg.MultiplexedSignals()
	if len(got) != 3 {
		t.Fatalf("expected 3 multiplexed signals, got %d", len(got))
	}
	names := make([]string, len(got))
	for i, s := range got {
		names[i] = string(s.Name)
	}
	want := []string{"Temperature", "Pressure", "RPM"}
	for i, w := range want {
		if names[i] != w {
			t.Errorf("got[%d].Name = %q, want %q", i, names[i], w)
		}
	}
}

func TestMultiplexorNames(t *testing.T) {
	msg := muxDBC().Messages[0]
	got := msg.MultiplexorNames()
	if len(got) != 1 {
		t.Fatalf("expected 1 multiplexor name, got %d", len(got))
	}
	if got[0] != "MuxSelector" {
		t.Errorf("got %q, want MuxSelector", got[0])
	}
}

func TestMuxValues(t *testing.T) {
	msg := muxDBC().Messages[0]
	got := msg.MuxValues("MuxSelector")
	if len(got) != 2 {
		t.Fatalf("expected 2 mux values, got %d", len(got))
	}
	if got[0] != 0 {
		t.Errorf("got[0] = %d, want 0", got[0])
	}
	if got[1] != 1 {
		t.Errorf("got[1] = %d, want 1", got[1])
	}
}

func TestMuxValues_UnknownMultiplexor(t *testing.T) {
	msg := muxDBC().Messages[0]
	got := msg.MuxValues("NonExistent")
	if got != nil {
		t.Errorf("expected nil for unknown multiplexor, got %v", got)
	}
}

func TestSignalsForMuxValue(t *testing.T) {
	msg := muxDBC().Messages[0]
	got := msg.SignalsForMuxValue("MuxSelector", 0)
	// Should include: MuxSelector (always), Temperature (mux=0), RPM (mux=0), Voltage (always)
	if len(got) != 4 {
		t.Fatalf("expected 4 signals for mux value 0, got %d", len(got))
	}
	names := make([]string, len(got))
	for i, s := range got {
		names[i] = string(s.Name)
	}
	want := []string{"MuxSelector", "Temperature", "RPM", "Voltage"}
	for i, w := range want {
		if names[i] != w {
			t.Errorf("got[%d].Name = %q, want %q", i, names[i], w)
		}
	}
}

func TestSignalsForMuxValue_OnlyAlways(t *testing.T) {
	msg := muxDBC().Messages[0]
	// Mux value 99 has no multiplexed signals — only always-present should return.
	got := msg.SignalsForMuxValue("MuxSelector", 99)
	if len(got) != 2 {
		t.Fatalf("expected 2 always-present signals for unknown mux value, got %d", len(got))
	}
	if got[0].Name != "MuxSelector" || got[1].Name != "Voltage" {
		t.Errorf("expected MuxSelector and Voltage, got %q and %q", got[0].Name, got[1].Name)
	}
}

func TestSignalsForMuxValue_Mux1(t *testing.T) {
	msg := muxDBC().Messages[0]
	got := msg.SignalsForMuxValue("MuxSelector", 1)
	// Should include: MuxSelector (always), Pressure (mux=1), Voltage (always)
	if len(got) != 3 {
		t.Fatalf("expected 3 signals for mux value 1, got %d", len(got))
	}
	if got[1].Name != "Pressure" {
		t.Errorf("expected Pressure as mux=1 signal, got %q", got[1].Name)
	}
}

func TestSignalsForMuxValue_UnknownMultiplexor(t *testing.T) {
	msg := muxDBC().Messages[0]
	// Non-existent multiplexor name — should return only always-present signals.
	got := msg.SignalsForMuxValue("NonExistent", 0)
	if len(got) != 2 {
		t.Fatalf("expected 2 always-present signals for unknown multiplexor, got %d", len(got))
	}
	if got[0].Name != "MuxSelector" || got[1].Name != "Voltage" {
		t.Errorf("expected MuxSelector and Voltage, got %q and %q", got[0].Name, got[1].Name)
	}
}

func TestIsMultiplexed_True(t *testing.T) {
	msg := muxDBC().Messages[0]
	if !msg.IsMultiplexed() {
		t.Error("expected IsMultiplexed() = true for mux message")
	}
}

func TestIsMultiplexed_False(t *testing.T) {
	msg := testDBC().Messages[0]
	if msg.IsMultiplexed() {
		t.Error("expected IsMultiplexed() = false for non-mux message")
	}
}

func TestAlwaysPresentSignals_NoMux(t *testing.T) {
	// Message with no multiplexed signals — all should be always-present.
	msg := testDBC().Messages[0]
	got := msg.AlwaysPresentSignals()
	if len(got) != len(msg.Signals) {
		t.Errorf("expected %d, got %d", len(msg.Signals), len(got))
	}
}

func TestMultiplexedSignals_NoMux(t *testing.T) {
	msg := testDBC().Messages[0]
	got := msg.MultiplexedSignals()
	if len(got) != 0 {
		t.Errorf("expected 0 multiplexed signals, got %d", len(got))
	}
}

func TestMultiplexorNames_NoMux(t *testing.T) {
	msg := testDBC().Messages[0]
	got := msg.MultiplexorNames()
	if len(got) != 0 {
		t.Errorf("expected 0 multiplexor names, got %d", len(got))
	}
}

// ---------------------------------------------------------------------------
// DbcDefinition lookup helpers
// ---------------------------------------------------------------------------

func TestMessageByID(t *testing.T) {
	dbc := muxDBC()
	sid, _ := aletheia.NewStandardID(0x200)
	msg := dbc.MessageByID(sid)
	if msg == nil {
		t.Fatal("expected non-nil message")
	}
	if msg.Name != "MuxMessage" {
		t.Errorf("got name %q, want MuxMessage", msg.Name)
	}
}

func TestMessageByID_NotFound(t *testing.T) {
	dbc := muxDBC()
	sid, _ := aletheia.NewStandardID(0x999)
	if dbc.MessageByID(sid) != nil {
		t.Error("expected nil for missing ID")
	}
}

func TestMessageByID_ExtendedVsStandard(t *testing.T) {
	// Standard ID 0x200 exists, but extended ID 0x200 should not match.
	dbc := muxDBC()
	eid, _ := aletheia.NewExtendedID(0x200)
	if dbc.MessageByID(eid) != nil {
		t.Error("expected nil: extended ID should not match standard ID message")
	}
}

func TestMessageByName(t *testing.T) {
	dbc := muxDBC()
	msg := dbc.MessageByName("MuxMessage")
	if msg == nil {
		t.Fatal("expected non-nil message")
	}
	if msg.ID.Value() != 0x200 {
		t.Errorf("got ID %d, want 0x200", msg.ID.Value())
	}
}

func TestMessageByName_NotFound(t *testing.T) {
	dbc := muxDBC()
	if dbc.MessageByName("NoSuchMessage") != nil {
		t.Error("expected nil for missing name")
	}
}

func TestMessageByID_CopyIndependence(t *testing.T) {
	dbc := muxDBC()
	sid, _ := aletheia.NewStandardID(0x200)
	msg := dbc.MessageByID(sid)
	if msg == nil {
		t.Fatal("expected non-nil message")
	}
	// Mutate the returned copy.
	msg.Name = "Modified"
	msg.Signals = nil
	// Original must be unaffected.
	original := dbc.MessageByID(sid)
	if original.Name == "Modified" {
		t.Error("mutation of returned copy affected the original name")
	}
	if len(original.Signals) == 0 {
		t.Error("mutation of returned copy affected the original signals")
	}
}

func TestMessageByName_CopyIndependence(t *testing.T) {
	dbc := muxDBC()
	msg := dbc.MessageByName("MuxMessage")
	if msg == nil {
		t.Fatal("expected non-nil message")
	}
	msg.Sender = "Modified"
	original := dbc.MessageByName("MuxMessage")
	if original.Sender == "Modified" {
		t.Error("mutation of returned copy affected the original sender")
	}
}

// ---------------------------------------------------------------------------
// Helpers
// ---------------------------------------------------------------------------

func mustStdID(v uint16) aletheia.CanID {
	id, err := aletheia.NewStandardID(v)
	if err != nil {
		panic(err)
	}
	return id
}

func mustDLC(v uint8) aletheia.DLC {
	d, err := aletheia.NewDLC(v)
	if err != nil {
		panic(err)
	}
	return d
}

// ---------------------------------------------------------------------------
// Additional coverage
// ---------------------------------------------------------------------------

func TestIsMultiplexed_EmptySignals(t *testing.T) {
	msg := aletheia.DbcMessage{
		ID:      mustStdID(0x300),
		Name:    "Empty",
		DLC:     mustDLC(8),
		Sender:  "ECU",
		Signals: nil,
	}
	if msg.IsMultiplexed() {
		t.Error("expected not multiplexed for empty signals")
	}
	if len(msg.AlwaysPresentSignals()) != 0 {
		t.Error("expected no always-present signals")
	}
	if len(msg.MultiplexedSignals()) != 0 {
		t.Error("expected no multiplexed signals")
	}
	if len(msg.MultiplexorNames()) != 0 {
		t.Error("expected no multiplexor names")
	}
}

func TestMultiplexorNames_MultipleMuxors(t *testing.T) {
	msg := aletheia.DbcMessage{
		ID: mustStdID(0x400), Name: "DualMux", DLC: mustDLC(8), Sender: "ECU",
		Signals: []aletheia.DbcSignal{
			{Name: "MuxA", Presence: aletheia.AlwaysPresent{}},
			{Name: "SigA1", Presence: aletheia.Multiplexed{Multiplexor: "MuxA", MuxValue: 0}},
			{Name: "MuxB", Presence: aletheia.AlwaysPresent{}},
			{Name: "SigB1", Presence: aletheia.Multiplexed{Multiplexor: "MuxB", MuxValue: 0}},
			{Name: "SigA2", Presence: aletheia.Multiplexed{Multiplexor: "MuxA", MuxValue: 1}},
		},
	}
	names := msg.MultiplexorNames()
	if len(names) != 2 {
		t.Fatalf("expected 2 multiplexor names, got %d", len(names))
	}
	if names[0] != "MuxA" || names[1] != "MuxB" {
		t.Errorf("expected [MuxA, MuxB], got %v", names)
	}
	// MuxValues for MuxA should be [0, 1]
	mv := msg.MuxValues("MuxA")
	if len(mv) != 2 || mv[0] != 0 || mv[1] != 1 {
		t.Errorf("expected MuxA values [0,1], got %v", mv)
	}
}

func TestMessageByID_MultipleMessages(t *testing.T) {
	dbc := aletheia.DbcDefinition{
		Version: "1.0",
		Messages: []aletheia.DbcMessage{
			{ID: mustStdID(0x100), Name: "First", DLC: mustDLC(8), Sender: "ECU"},
			{ID: mustStdID(0x200), Name: "Second", DLC: mustDLC(8), Sender: "ECU"},
			{ID: mustStdID(0x300), Name: "Third", DLC: mustDLC(8), Sender: "ECU"},
		},
	}
	msg := dbc.MessageByID(mustStdID(0x200))
	if msg == nil {
		t.Fatal("expected to find message 0x200")
	}
	if msg.Name != "Second" {
		t.Errorf("expected Second, got %s", msg.Name)
	}
}

func TestMessageByName_MultipleMessages(t *testing.T) {
	dbc := aletheia.DbcDefinition{
		Version: "1.0",
		Messages: []aletheia.DbcMessage{
			{ID: mustStdID(0x100), Name: "First", DLC: mustDLC(8), Sender: "ECU"},
			{ID: mustStdID(0x200), Name: "Second", DLC: mustDLC(8), Sender: "ECU"},
		},
	}
	msg := dbc.MessageByName("First")
	if msg == nil {
		t.Fatal("expected to find message First")
	}
	if string(msg.Name) != "First" {
		t.Errorf("expected First, got %s", msg.Name)
	}
}

func TestSignalByName(t *testing.T) {
	msg := muxDBC().Messages[0]
	sig := msg.SignalByName("Temperature")
	if sig == nil {
		t.Fatal("expected to find Temperature")
	}
	if !sig.IsSigned {
		t.Error("expected Temperature to be signed")
	}
	// Mutation of returned signal should not affect original.
	sig.Name = "Modified"
	orig := msg.SignalByName("Temperature")
	if orig == nil {
		t.Fatal("expected Temperature still exists")
	}
	if string(orig.Name) != "Temperature" {
		t.Errorf("expected Temperature, got %s", orig.Name)
	}

	if msg.SignalByName("NoSuch") != nil {
		t.Error("expected nil for non-existent signal")
	}
}
