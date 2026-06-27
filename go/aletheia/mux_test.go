// SPDX-FileCopyrightText: 2025 Nicolas Pelletier
// SPDX-License-Identifier: BSD-2-Clause

package aletheia_test

import (
	"slices"
	"testing"

	"github.com/aletheia-automotive/aletheia-go/aletheia"
)

// muxDBC returns a DBC with multiplexed signals for testing.
func muxDBC() aletheia.DBCDefinition {
	sid, _ := aletheia.NewStandardID(0x200)
	dlc, _ := aletheia.NewDLC(8)
	return aletheia.DBCDefinition{
		Version: "1.0",
		Messages: []aletheia.DBCMessage{
			{
				ID: sid, Name: "MuxMessage", DLC: dlc, Sender: "ECU",
				Signals: []aletheia.DBCSignal{
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
						Unit: "degC", Presence: aletheia.Multiplexed{Multiplexor: "MuxSelector", MultiplexValues: []aletheia.MultiplexValue{0}},
					},
					{
						Name: "Pressure", StartBit: 8, BitLength: 16,
						ByteOrder: aletheia.LittleEndian, IsSigned: false,
						Factor: aletheia.Rational{Numerator: 1, Denominator: 100}, Offset: aletheia.Rational{Numerator: 0, Denominator: 1}, Minimum: aletheia.Rational{Numerator: 0, Denominator: 1}, Maximum: aletheia.Rational{Numerator: 655, Denominator: 1},
						Unit: "bar", Presence: aletheia.Multiplexed{Multiplexor: "MuxSelector", MultiplexValues: []aletheia.MultiplexValue{1}},
					},
					{
						Name: "RPM", StartBit: 24, BitLength: 16,
						ByteOrder: aletheia.LittleEndian, IsSigned: false,
						Factor: aletheia.Rational{Numerator: 1, Denominator: 1}, Offset: aletheia.Rational{Numerator: 0, Denominator: 1}, Minimum: aletheia.Rational{Numerator: 0, Denominator: 1}, Maximum: aletheia.Rational{Numerator: 10000, Denominator: 1},
						Unit: "rpm", Presence: aletheia.Multiplexed{Multiplexor: "MuxSelector", MultiplexValues: []aletheia.MultiplexValue{0}},
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

func TestMultiplexValues(t *testing.T) {
	msg := muxDBC().Messages[0]
	got := msg.MultiplexValues("MuxSelector")
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

func TestMultiplexValues_UnknownMultiplexor(t *testing.T) {
	msg := muxDBC().Messages[0]
	got := msg.MultiplexValues("NonExistent")
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
// DBCDefinition lookup helpers
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

// richCopyDBC returns a single-message DBC whose every reference-typed field is
// non-empty — Senders, each signal's Receivers / ValueDescriptions, and a
// Multiplexed signal's MultiplexValues — so the deep-copy independence test below
// is not silently vacuous on an empty slice.
func richCopyDBC() aletheia.DBCDefinition {
	return aletheia.DBCDefinition{
		Version: "1.0",
		Messages: []aletheia.DBCMessage{
			{
				ID: mustStdID(0x310), Name: "Rich", DLC: mustDLC(8), Sender: "ECU",
				Senders: []string{"GW", "BCM"},
				Signals: []aletheia.DBCSignal{
					{
						Name: "Mode", StartBit: 0, BitLength: 8,
						ByteOrder: aletheia.LittleEndian,
						Factor:    aletheia.Rational{Numerator: 1, Denominator: 1},
						Offset:    aletheia.Rational{Numerator: 0, Denominator: 1},
						Minimum:   aletheia.Rational{Numerator: 0, Denominator: 1},
						Maximum:   aletheia.Rational{Numerator: 3, Denominator: 1},
						Presence:  aletheia.AlwaysPresent{},
						Receivers: []string{"NodeA", "NodeB"},
						ValueDescriptions: []aletheia.DBCValueEntry{
							{Value: 0, Description: "off"},
							{Value: 1, Description: "on"},
						},
					},
					{
						Name: "Level", StartBit: 8, BitLength: 16,
						ByteOrder: aletheia.LittleEndian,
						Factor:    aletheia.Rational{Numerator: 1, Denominator: 1},
						Offset:    aletheia.Rational{Numerator: 0, Denominator: 1},
						Minimum:   aletheia.Rational{Numerator: 0, Denominator: 1},
						Maximum:   aletheia.Rational{Numerator: 100, Denominator: 1},
						Presence: aletheia.Multiplexed{
							Multiplexor:     "Mode",
							MultiplexValues: []aletheia.MultiplexValue{0, 1},
						},
						Receivers: []string{"NodeC"},
					},
				},
			},
		},
	}
}

// TestMessageByName_DeepCopyIndependence pins copyMessage as a TRUE deep copy:
// every reference field is cloned, so a caller mutating a nested backing array of
// the returned message cannot reach the DBC's stored definition. The content-
// equality block guards the converse — that the clone is faithful, not garbage
// (and that an AlwaysPresent presence is not clobbered into a zero Multiplexed).
func TestMessageByName_DeepCopyIndependence(t *testing.T) {
	dbc := richCopyDBC()
	orig := &dbc.Messages[0]

	cp := dbc.MessageByName("Rich")
	if cp == nil {
		t.Fatal("expected non-nil message")
	}
	if !slices.Equal(cp.Senders, orig.Senders) {
		t.Errorf("Senders not copied faithfully: %v vs %v", cp.Senders, orig.Senders)
	}
	if !slices.Equal(cp.Signals[0].Receivers, orig.Signals[0].Receivers) {
		t.Error("Receivers not copied faithfully")
	}
	if !slices.Equal(cp.Signals[0].ValueDescriptions, orig.Signals[0].ValueDescriptions) {
		t.Error("ValueDescriptions not copied faithfully")
	}
	cpMux := muxOf(t, "copy signal[1]", cp.Signals[1])
	origMux := muxOf(t, "orig signal[1]", orig.Signals[1])
	if !slices.Equal(cpMux.MultiplexValues, origMux.MultiplexValues) {
		t.Error("MultiplexValues not copied faithfully")
	}
	if _, ok := cp.Signals[0].Presence.(aletheia.AlwaysPresent); !ok {
		t.Errorf("AlwaysPresent presence not preserved in the copy: got %T", cp.Signals[0].Presence)
	}

	t.Run("Senders", func(t *testing.T) {
		c := dbc.MessageByName("Rich")
		c.Senders[0] = "MUTATED"
		if dbc.Messages[0].Senders[0] == "MUTATED" {
			t.Error("mutating the copy's Senders backing array affected the original")
		}
	})
	t.Run("Receivers", func(t *testing.T) {
		c := dbc.MessageByName("Rich")
		c.Signals[0].Receivers[0] = "MUTATED"
		if dbc.Messages[0].Signals[0].Receivers[0] == "MUTATED" {
			t.Error("mutating the copy's Receivers backing array affected the original")
		}
	})
	t.Run("ValueDescriptions", func(t *testing.T) {
		c := dbc.MessageByName("Rich")
		c.Signals[0].ValueDescriptions[0].Description = "MUTATED"
		if dbc.Messages[0].Signals[0].ValueDescriptions[0].Description == "MUTATED" {
			t.Error("mutating the copy's ValueDescriptions backing array affected the original")
		}
	})
	t.Run("MultiplexValues", func(t *testing.T) {
		c := dbc.MessageByName("Rich")
		if c == nil {
			t.Fatal("expected non-nil message")
		}
		mux := muxOf(t, "copy signal[1]", c.Signals[1])
		mux.MultiplexValues[0] = 99
		got := muxOf(t, "orig signal[1]", dbc.Messages[0].Signals[1]).MultiplexValues[0]
		if got == 99 {
			t.Error("mutating the copy's MultiplexValues backing array affected the original")
		}
	})
}

// muxOf returns the value-form Multiplexed presence of sig, failing the test
// (rather than panicking on an unchecked assertion) if it was clobbered.
func muxOf(t *testing.T, label string, sig aletheia.DBCSignal) aletheia.Multiplexed {
	t.Helper()
	mux, ok := sig.Presence.(aletheia.Multiplexed)
	if !ok {
		t.Fatalf("%s: presence is %T, want Multiplexed", label, sig.Presence)
	}
	return mux
}

// TestCopyMessage_PointerMultiplexedDeepCopy covers the *Multiplexed presence
// form. SignalPresence is sealed by a value-receiver method, so *Multiplexed also
// satisfies it and a manually constructed signal may hold Presence:
// &Multiplexed{...}; copyMessage must clone its MultiplexValues too, not alias.
func TestCopyMessage_PointerMultiplexedDeepCopy(t *testing.T) {
	dbc := aletheia.DBCDefinition{
		Version: "1.0",
		Messages: []aletheia.DBCMessage{{
			ID: mustStdID(0x320), Name: "PtrMux", DLC: mustDLC(8), Sender: "ECU",
			Signals: []aletheia.DBCSignal{{
				Name: "Sel", StartBit: 0, BitLength: 8,
				ByteOrder: aletheia.LittleEndian,
				Factor:    aletheia.Rational{Numerator: 1, Denominator: 1},
				Offset:    aletheia.Rational{Numerator: 0, Denominator: 1},
				Minimum:   aletheia.Rational{Numerator: 0, Denominator: 1},
				Maximum:   aletheia.Rational{Numerator: 7, Denominator: 1},
				Presence: &aletheia.Multiplexed{
					Multiplexor:     "Sel",
					MultiplexValues: []aletheia.MultiplexValue{3, 4},
				},
			}},
		}},
	}
	c := dbc.MessageByName("PtrMux")
	if c == nil {
		t.Fatal("expected non-nil message")
	}
	cpMux, ok := c.Signals[0].Presence.(*aletheia.Multiplexed)
	if !ok {
		t.Fatalf("copy presence: got %T, want *Multiplexed", c.Signals[0].Presence)
	}
	cpMux.MultiplexValues[0] = 99
	origMux, ok := dbc.Messages[0].Signals[0].Presence.(*aletheia.Multiplexed)
	if !ok {
		t.Fatalf("orig presence: got %T, want *Multiplexed", dbc.Messages[0].Signals[0].Presence)
	}
	if origMux.MultiplexValues[0] == 99 {
		t.Error("mutating the copy's *Multiplexed MultiplexValues affected the original")
	}
}

// ---------------------------------------------------------------------------
// Helpers
// ---------------------------------------------------------------------------

// mustStdID builds a standard-frame CANID from a raw 11-bit value in
// tests; panics on out-of-range input because test fixtures should
// never produce one and the panic message is more useful than a
// silently-propagated error.
func mustStdID(v uint16) aletheia.CANID {
	id, err := aletheia.NewStandardID(v)
	if err != nil {
		panic(err)
	}
	return id
}

// mustDLC builds a DLC newtype in tests; panics on out-of-range input
// for the same reason as mustStdID.
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
	msg := aletheia.DBCMessage{
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
	msg := aletheia.DBCMessage{
		ID: mustStdID(0x400), Name: "DualMux", DLC: mustDLC(8), Sender: "ECU",
		Signals: []aletheia.DBCSignal{
			{Name: "MuxA", Presence: aletheia.AlwaysPresent{}},
			{Name: "SigA1", Presence: aletheia.Multiplexed{Multiplexor: "MuxA", MultiplexValues: []aletheia.MultiplexValue{0}}},
			{Name: "MuxB", Presence: aletheia.AlwaysPresent{}},
			{Name: "SigB1", Presence: aletheia.Multiplexed{Multiplexor: "MuxB", MultiplexValues: []aletheia.MultiplexValue{0}}},
			{Name: "SigA2", Presence: aletheia.Multiplexed{Multiplexor: "MuxA", MultiplexValues: []aletheia.MultiplexValue{1}}},
		},
	}
	names := msg.MultiplexorNames()
	if len(names) != 2 {
		t.Fatalf("expected 2 multiplexor names, got %d", len(names))
	}
	if names[0] != "MuxA" || names[1] != "MuxB" {
		t.Errorf("expected [MuxA, MuxB], got %v", names)
	}
	// MultiplexValues for MuxA should be [0, 1]
	mv := msg.MultiplexValues("MuxA")
	if len(mv) != 2 || mv[0] != 0 || mv[1] != 1 {
		t.Errorf("expected MuxA values [0,1], got %v", mv)
	}
}

func TestMessageByID_MultipleMessages(t *testing.T) {
	dbc := aletheia.DBCDefinition{
		Version: "1.0",
		Messages: []aletheia.DBCMessage{
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
	dbc := aletheia.DBCDefinition{
		Version: "1.0",
		Messages: []aletheia.DBCMessage{
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
