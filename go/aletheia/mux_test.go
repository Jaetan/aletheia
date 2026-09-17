// SPDX-FileCopyrightText: 2025 Nicolas Pelletier
// SPDX-License-Identifier: BSD-2-Clause

package aletheia_test

import (
	"slices"
	"testing"

	"github.com/aletheia-automotive/aletheia-go/aletheia"
)

// ratOf is the exact rational n over d.
func ratOf(n, d int64) aletheia.Rational { return aletheia.Rational{Numerator: n, Denominator: d} }

// muxDBC is one message carrying two signals that are always there and three
// that depend on a selector: two under value zero and one under value one.
func muxDBC() aletheia.DBCDefinition {
	sid, _ := aletheia.NewStandardID(0x200)
	dlc, _ := aletheia.NewDLC(8)
	under := func(value aletheia.MultiplexValue) aletheia.SignalPresence {
		return aletheia.Multiplexed{Multiplexor: "MuxSelector", MultiplexValues: []aletheia.MultiplexValue{value}}
	}
	return aletheia.DBCDefinition{
		Version: "1.0",
		Messages: []aletheia.DBCMessage{
			{
				ID: sid, Name: "MuxMessage", DLC: dlc, Sender: "ECU",
				Signals: []aletheia.DBCSignal{
					{
						Name: "MuxSelector", StartBit: 0, BitLength: 8,
						ByteOrder: aletheia.LittleEndian,
						Factor:    ratOf(1, 1), Offset: ratOf(0, 1), Minimum: ratOf(0, 1), Maximum: ratOf(255, 1),
						Presence: aletheia.AlwaysPresent{},
					},
					{
						Name: "Temperature", StartBit: 8, BitLength: 16, IsSigned: true,
						ByteOrder: aletheia.LittleEndian,
						Factor:    ratOf(1, 10), Offset: ratOf(-40, 1), Minimum: ratOf(-40, 1), Maximum: ratOf(215, 1),
						Unit: "degC", Presence: under(0),
					},
					{
						Name: "Pressure", StartBit: 8, BitLength: 16,
						ByteOrder: aletheia.LittleEndian,
						Factor:    ratOf(1, 100), Offset: ratOf(0, 1), Minimum: ratOf(0, 1), Maximum: ratOf(655, 1),
						Unit: "bar", Presence: under(1),
					},
					{
						Name: "RPM", StartBit: 24, BitLength: 16,
						ByteOrder: aletheia.LittleEndian,
						Factor:    ratOf(1, 1), Offset: ratOf(0, 1), Minimum: ratOf(0, 1), Maximum: ratOf(10000, 1),
						Unit: "rpm", Presence: under(0),
					},
					{
						Name: "Voltage", StartBit: 40, BitLength: 16,
						ByteOrder: aletheia.LittleEndian,
						Factor:    ratOf(1, 100), Offset: ratOf(0, 1), Minimum: ratOf(0, 1), Maximum: ratOf(65, 1),
						Unit: "V", Presence: aletheia.AlwaysPresent{},
					},
				},
			},
		},
	}
}

// signalNames is the names of the signals, in the order the accessor gave them.
func signalNames(signals []aletheia.DBCSignal) []string {
	out := make([]string, len(signals))
	for i, s := range signals {
		out[i] = string(s.Name)
	}
	return out
}

// The three accessors that partition a message's signals answer in the order
// the definition declares them, and answer nothing on a message with no
// multiplexing at all.
func TestMessage_SignalPartitions(t *testing.T) {
	mux := muxDBC().Messages[0]
	plain := testDBC().Messages[0]
	cases := map[string]struct {
		got  []string
		want []string
	}{
		"always present, multiplexed message": {signalNames(mux.AlwaysPresentSignals()), []string{"MuxSelector", "Voltage"}},
		"multiplexed, multiplexed message":    {signalNames(mux.MultiplexedSignals()), []string{"Temperature", "Pressure", "RPM"}},
		"always present, plain message":       {signalNames(plain.AlwaysPresentSignals()), signalNames(plain.Signals)},
		"multiplexed, plain message":          {signalNames(plain.MultiplexedSignals()), []string{}},
	}
	for name, tc := range cases {
		t.Run(name, func(t *testing.T) {
			if !slices.Equal(tc.got, tc.want) && !(len(tc.got) == 0 && len(tc.want) == 0) {
				t.Errorf("got %v, want %v", tc.got, tc.want)
			}
		})
	}
}

// The multiplexors of a message are named once each, in declaration order,
// and a message with none names none.
func TestMessage_MultiplexorNames(t *testing.T) {
	dual := aletheia.DBCMessage{
		ID: mustStdID(0x400), Name: "DualMux", DLC: mustDLC(8), Sender: "ECU",
		Signals: []aletheia.DBCSignal{
			{Name: "MuxA", Presence: aletheia.AlwaysPresent{}},
			{Name: "SigA1", Presence: aletheia.Multiplexed{Multiplexor: "MuxA", MultiplexValues: []aletheia.MultiplexValue{0}}},
			{Name: "MuxB", Presence: aletheia.AlwaysPresent{}},
			{Name: "SigB1", Presence: aletheia.Multiplexed{Multiplexor: "MuxB", MultiplexValues: []aletheia.MultiplexValue{0}}},
			{Name: "SigA2", Presence: aletheia.Multiplexed{Multiplexor: "MuxA", MultiplexValues: []aletheia.MultiplexValue{1}}},
		},
	}
	cases := map[string]struct {
		message aletheia.DBCMessage
		want    []aletheia.SignalName
	}{
		"one multiplexor":  {muxDBC().Messages[0], []aletheia.SignalName{"MuxSelector"}},
		"two multiplexors": {dual, []aletheia.SignalName{"MuxA", "MuxB"}},
		"none":             {testDBC().Messages[0], nil},
	}
	for name, tc := range cases {
		t.Run(name, func(t *testing.T) {
			got := tc.message.MultiplexorNames()
			if len(got) != len(tc.want) {
				t.Fatalf("got %v, want %v", got, tc.want)
			}
			for i := range got {
				if got[i] != tc.want[i] {
					t.Errorf("got[%d] = %q, want %q", i, got[i], tc.want[i])
				}
			}
		})
	}
}

// The values a multiplexor selects are those its signals declare, in order,
// and a name that multiplexes nothing selects nothing.
func TestMessage_MultiplexValues(t *testing.T) {
	msg := muxDBC().Messages[0]
	cases := map[string]struct {
		multiplexor aletheia.SignalName
		want        []aletheia.MultiplexValue
	}{
		"the message's multiplexor": {"MuxSelector", []aletheia.MultiplexValue{0, 1}},
		"a name that is not one":    {"NonExistent", nil},
	}
	for name, tc := range cases {
		t.Run(name, func(t *testing.T) {
			if got := msg.MultiplexValues(tc.multiplexor); !slices.Equal(got, tc.want) {
				t.Errorf("got %v, want %v", got, tc.want)
			}
		})
	}
	dual := aletheia.DBCMessage{
		ID: mustStdID(0x400), Name: "DualMux", DLC: mustDLC(8), Sender: "ECU",
		Signals: []aletheia.DBCSignal{
			{Name: "MuxA", Presence: aletheia.AlwaysPresent{}},
			{Name: "SigA1", Presence: aletheia.Multiplexed{Multiplexor: "MuxA", MultiplexValues: []aletheia.MultiplexValue{0}}},
			{Name: "SigA2", Presence: aletheia.Multiplexed{Multiplexor: "MuxA", MultiplexValues: []aletheia.MultiplexValue{1}}},
		},
	}
	if got := dual.MultiplexValues("MuxA"); !slices.Equal(got, []aletheia.MultiplexValue{0, 1}) {
		t.Errorf("values across two signals: got %v, want [0 1]", got)
	}
}

// The signals present at a selector value are the ones always there plus the
// ones that value selects, in declaration order. A value nothing selects, and
// a multiplexor that is not one, leave only the signals always there.
func TestMessage_SignalsForMuxValue(t *testing.T) {
	msg := muxDBC().Messages[0]
	cases := map[string]struct {
		multiplexor aletheia.SignalName
		value       aletheia.MultiplexValue
		want        []string
	}{
		"the first value":         {"MuxSelector", 0, []string{"MuxSelector", "Temperature", "RPM", "Voltage"}},
		"the second":              {"MuxSelector", 1, []string{"MuxSelector", "Pressure", "Voltage"}},
		"a value nothing selects": {"MuxSelector", 99, []string{"MuxSelector", "Voltage"}},
		"a name that is not one":  {"NonExistent", 0, []string{"MuxSelector", "Voltage"}},
	}
	for name, tc := range cases {
		t.Run(name, func(t *testing.T) {
			if got := signalNames(msg.SignalsForMuxValue(tc.multiplexor, tc.value)); !slices.Equal(got, tc.want) {
				t.Errorf("got %v, want %v", got, tc.want)
			}
		})
	}
}

// A message is multiplexed when any signal depends on a selector.
func TestMessage_IsMultiplexed(t *testing.T) {
	empty := aletheia.DBCMessage{ID: mustStdID(0x300), Name: "Empty", DLC: mustDLC(8), Sender: "ECU"}
	cases := map[string]struct {
		message aletheia.DBCMessage
		want    bool
	}{
		"with multiplexed signals": {muxDBC().Messages[0], true},
		"with none":                {testDBC().Messages[0], false},
		"with no signals at all":   {empty, false},
	}
	for name, tc := range cases {
		t.Run(name, func(t *testing.T) {
			if got := tc.message.IsMultiplexed(); got != tc.want {
				t.Errorf("got %v, want %v", got, tc.want)
			}
		})
	}
	if len(empty.AlwaysPresentSignals()) != 0 || len(empty.MultiplexedSignals()) != 0 || len(empty.MultiplexorNames()) != 0 {
		t.Error("a message with no signals partitions into something")
	}
}

// A message is found by its identifier or by its name, and an extended
// identifier of the same number is a different message.
func TestDefinition_MessageLookup(t *testing.T) {
	dbc := aletheia.DBCDefinition{
		Version: "1.0",
		Messages: []aletheia.DBCMessage{
			{ID: mustStdID(0x100), Name: "First", DLC: mustDLC(8), Sender: "ECU"},
			{ID: mustStdID(0x200), Name: "Second", DLC: mustDLC(8), Sender: "ECU"},
			{ID: mustStdID(0x300), Name: "Third", DLC: mustDLC(8), Sender: "ECU"},
		},
	}
	extended, err := aletheia.NewExtendedID(0x200)
	if err != nil {
		t.Fatalf("NewExtendedID: %v", err)
	}
	byID := map[string]struct {
		id   aletheia.CANID
		want string
	}{
		"the first":                     {mustStdID(0x100), "First"},
		"one in the middle":             {mustStdID(0x200), "Second"},
		"one that is not there":         {mustStdID(0x7FF), ""},
		"an extended identifier of one": {extended, ""},
	}
	for name, tc := range byID {
		t.Run(name, func(t *testing.T) {
			msg := dbc.MessageByID(tc.id)
			switch {
			case tc.want == "" && msg != nil:
				t.Errorf("found %q for an identifier no message has", msg.Name)
			case tc.want != "" && msg == nil:
				t.Errorf("found nothing, want %q", tc.want)
			case tc.want != "" && string(msg.Name) != tc.want:
				t.Errorf("found %q, want %q", msg.Name, tc.want)
			}
		})
	}
	byName := map[string]string{"First": "First", "Third": "Third", "NoSuchMessage": ""}
	for query, want := range byName {
		t.Run("by name "+query, func(t *testing.T) {
			msg := dbc.MessageByName(aletheia.MessageName(query))
			switch {
			case want == "" && msg != nil:
				t.Errorf("found %q for a name no message has", msg.Name)
			case want != "" && (msg == nil || string(msg.Name) != want):
				t.Errorf("found %v, want %q", msg, want)
			}
		})
	}
}

// A message read out of a definition is a copy: editing it, however deeply,
// leaves the definition as it was. The equality checks below are the other
// half, that the copy is faithful rather than empty, and that a signal that is
// always present does not come back multiplexed.
func TestDefinition_MessageIsADeepCopy(t *testing.T) {
	dbc := richCopyDBC()
	orig := &dbc.Messages[0]

	cp := dbc.MessageByName("Rich")
	if cp == nil {
		t.Fatal("expected a message")
	}
	if !slices.Equal(cp.Senders, orig.Senders) {
		t.Errorf("senders: %v, want %v", cp.Senders, orig.Senders)
	}
	if !slices.Equal(cp.Signals[0].Receivers, orig.Signals[0].Receivers) {
		t.Error("the receivers did not come across")
	}
	if !slices.Equal(cp.Signals[0].ValueDescriptions, orig.Signals[0].ValueDescriptions) {
		t.Error("the value descriptions did not come across")
	}
	if !slices.Equal(muxOf(t, "the copy", cp.Signals[1]).MultiplexValues,
		muxOf(t, "the original", orig.Signals[1]).MultiplexValues) {
		t.Error("the multiplex values did not come across")
	}
	if _, ok := cp.Signals[0].Presence.(aletheia.AlwaysPresent); !ok {
		t.Errorf("an always-present signal came back as %T", cp.Signals[0].Presence)
	}

	edits := map[string]struct {
		edit  func(*aletheia.DBCMessage)
		check func(*aletheia.DBCMessage) bool
	}{
		"senders": {
			func(m *aletheia.DBCMessage) { m.Senders[0] = "MUTATED" },
			func(m *aletheia.DBCMessage) bool { return m.Senders[0] == "MUTATED" },
		},
		"receivers": {
			func(m *aletheia.DBCMessage) { m.Signals[0].Receivers[0] = "MUTATED" },
			func(m *aletheia.DBCMessage) bool { return m.Signals[0].Receivers[0] == "MUTATED" },
		},
		"value descriptions": {
			func(m *aletheia.DBCMessage) { m.Signals[0].ValueDescriptions[0].Description = "MUTATED" },
			func(m *aletheia.DBCMessage) bool { return m.Signals[0].ValueDescriptions[0].Description == "MUTATED" },
		},
		"multiplex values": {
			func(m *aletheia.DBCMessage) {
				mux, ok := m.Signals[1].Presence.(aletheia.Multiplexed)
				if ok {
					mux.MultiplexValues[0] = 99
				}
			},
			func(m *aletheia.DBCMessage) bool {
				mux, ok := m.Signals[1].Presence.(aletheia.Multiplexed)
				return ok && mux.MultiplexValues[0] == 99
			},
		},
		"the name and the signals": {
			func(m *aletheia.DBCMessage) { m.Name = "MUTATED"; m.Signals = nil },
			func(m *aletheia.DBCMessage) bool { return m.Name == "MUTATED" || len(m.Signals) == 0 },
		},
	}
	for what, tc := range edits {
		t.Run(what, func(t *testing.T) {
			c := dbc.MessageByName("Rich")
			if c == nil {
				t.Fatal("expected a message")
			}
			tc.edit(c)
			if tc.check(&dbc.Messages[0]) {
				t.Errorf("editing the copy's %s reached the definition", what)
			}
		})
	}
}

// A presence held as a pointer is copied as deeply as one held as a value:
// the interface is satisfied by both, so a definition built by hand may carry
// either.
func TestDefinition_PointerPresenceIsCopiedToo(t *testing.T) {
	dbc := aletheia.DBCDefinition{
		Version: "1.0",
		Messages: []aletheia.DBCMessage{{
			ID: mustStdID(0x320), Name: "PtrMux", DLC: mustDLC(8), Sender: "ECU",
			Signals: []aletheia.DBCSignal{{
				Name: "Sel", StartBit: 0, BitLength: 8,
				ByteOrder: aletheia.LittleEndian,
				Factor:    ratOf(1, 1), Offset: ratOf(0, 1), Minimum: ratOf(0, 1), Maximum: ratOf(7, 1),
				Presence: &aletheia.Multiplexed{
					Multiplexor:     "Sel",
					MultiplexValues: []aletheia.MultiplexValue{3, 4},
				},
			}},
		}},
	}
	c := dbc.MessageByName("PtrMux")
	if c == nil {
		t.Fatal("expected a message")
	}
	cpMux, ok := c.Signals[0].Presence.(*aletheia.Multiplexed)
	if !ok {
		t.Fatalf("the copy's presence is %T, want a pointer to Multiplexed", c.Signals[0].Presence)
	}
	cpMux.MultiplexValues[0] = 99
	origMux, ok := dbc.Messages[0].Signals[0].Presence.(*aletheia.Multiplexed)
	if !ok {
		t.Fatalf("the original's presence is %T, want a pointer to Multiplexed", dbc.Messages[0].Signals[0].Presence)
	}
	if origMux.MultiplexValues[0] == 99 {
		t.Error("editing the copy's values reached the definition")
	}
}

// A signal is found by name within a message, as a copy, and a name no signal
// has finds nothing.
func TestMessage_SignalByName(t *testing.T) {
	msg := muxDBC().Messages[0]
	sig := msg.SignalByName("Temperature")
	if sig == nil {
		t.Fatal("expected to find Temperature")
	}
	if !sig.IsSigned {
		t.Error("Temperature came back unsigned")
	}
	sig.Name = "Modified"
	if again := msg.SignalByName("Temperature"); again == nil || string(again.Name) != "Temperature" {
		t.Errorf("editing the copy reached the message: %v", again)
	}
	if msg.SignalByName("NoSuch") != nil {
		t.Error("found a signal for a name none has")
	}
}

// richCopyDBC is one message whose every field that holds a reference is
// filled, so the copy test above cannot pass over an empty slice.
func richCopyDBC() aletheia.DBCDefinition {
	return aletheia.DBCDefinition{
		Version: "1.0",
		Messages: []aletheia.DBCMessage{
			{
				ID: mustStdID(0x310), Name: "Rich", DLC: mustDLC(8), Sender: "ECU",
				Senders: []aletheia.NodeName{"GW", "BCM"},
				Signals: []aletheia.DBCSignal{
					{
						Name: "Mode", StartBit: 0, BitLength: 8,
						ByteOrder: aletheia.LittleEndian,
						Factor:    ratOf(1, 1), Offset: ratOf(0, 1), Minimum: ratOf(0, 1), Maximum: ratOf(3, 1),
						Presence:  aletheia.AlwaysPresent{},
						Receivers: []aletheia.NodeName{"NodeA", "NodeB"},
						ValueDescriptions: []aletheia.DBCValueEntry{
							{Value: 0, Description: "off"},
							{Value: 1, Description: "on"},
						},
					},
					{
						Name: "Level", StartBit: 8, BitLength: 16,
						ByteOrder: aletheia.LittleEndian,
						Factor:    ratOf(1, 1), Offset: ratOf(0, 1), Minimum: ratOf(0, 1), Maximum: ratOf(100, 1),
						Presence: aletheia.Multiplexed{
							Multiplexor:     "Mode",
							MultiplexValues: []aletheia.MultiplexValue{0, 1},
						},
						Receivers: []aletheia.NodeName{"NodeC"},
					},
				},
			},
		},
	}
}

// muxOf is the multiplexed presence of a signal, failing the test rather than
// panicking when it is another kind.
func muxOf(t *testing.T, label string, sig aletheia.DBCSignal) aletheia.Multiplexed {
	t.Helper()
	mux, ok := sig.Presence.(aletheia.Multiplexed)
	if !ok {
		t.Fatalf("%s: presence is %T, want Multiplexed", label, sig.Presence)
	}
	return mux
}

// mustStdID and mustDLC build the two newtypes from values a fixture chose,
// panicking rather than returning an error: a fixture out of range is a
// mistake in the test, and the panic names it where it is written.
func mustStdID(v uint16) aletheia.CANID {
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
