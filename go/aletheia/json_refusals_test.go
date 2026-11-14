// SPDX-FileCopyrightText: 2025 Nicolas Pelletier
// SPDX-License-Identifier: BSD-2-Clause

package aletheia

import (
	"encoding/json"
	"errors"
	"math"
	"slices"
	"strconv"
	"testing"
)

// The encoder refuses a string that is not valid UTF-8 wherever it sits in a
// command, naming the place, rather than sending it altered: the peer
// bindings refuse the same input.
func TestRefuseInvalidUTF8_NamesWhereTheBytesSit(t *testing.T) {
	bad := "\xff"
	cases := map[string]struct {
		value any
		want  string
	}{
		"a string":            {bad, "command is not valid UTF-8"},
		"a raw message":       {json.RawMessage(bad), "command is not valid UTF-8"},
		"a key":               {map[string]any{bad: 1}, "command: a key is not valid UTF-8"},
		"a value under a key": {map[string]any{"dbc": bad}, "command.dbc is not valid UTF-8"},
		"an element":          {[]any{"ok", bad}, "command[1] is not valid UTF-8"},
		"a string element":    {[]string{bad}, "command[0] is not valid UTF-8"},
		"an object element":   {[]map[string]any{{"name": bad}}, "command[0].name is not valid UTF-8"},
	}
	for name, tc := range cases {
		t.Run(name, func(t *testing.T) {
			err := refuseInvalidUTF8("command", tc.value)
			requireErrorContains(t, err, tc.want)
			var e *Error
			if !errors.As(err, &e) || e.Kind != ErrValidation {
				t.Errorf("got %v, want a validation error", err)
			}
		})
	}
	if err := refuseInvalidUTF8("command", map[string]any{"a": []any{"b", []string{"c"}, 1}}); err != nil {
		t.Errorf("valid text refused: %v", err)
	}
}

// A definition whose signal carries a byte order outside the two the wire
// has does not marshal: the refusal reaches the caller of json.Marshal.
func TestDBCDefinition_MarshalJSONRefusesWhatTheWireCannotCarry(t *testing.T) {
	dbc := testDefinition()
	dbc.Messages[0].Signals[0].ByteOrder = ByteOrder(99)
	if _, err := json.Marshal(dbc); err == nil {
		t.Fatal("a signal with an unknown byte order marshalled")
	}
	if _, err := json.Marshal(testDefinition()); err != nil {
		t.Fatalf("the definition as built did not marshal: %v", err)
	}
}

// An unresolved value description reads its identifier at the width its
// flag names, the kernel proving the range, and its entries' signed keys; a
// fractional entry value and an identifier that is not a number are refused
// at their places.
func TestParseUnresolvedValueDesc_ReadsItsIdentifierAndEntries(t *testing.T) {
	const path = "dbc/unresolvedValueDescs"
	entry := map[string]any{"value": json.Number("-2"), "description": "Reverse"}
	raw := map[string]any{
		"id": json.Number(strconv.Itoa(1<<29 - 1)), "extended": true, "signalName": "Speed", "entries": []any{entry},
	}
	desc, err := parseUnresolvedValueDesc(raw, path)
	if err != nil || !desc.ID.IsExtended() || desc.ID.Value() != 1<<29-1 {
		t.Fatalf("the largest extended identifier was not read back: %v, %v", desc, err)
	}
	want := DBCValueEntry{Value: SignMagnitude{Negative: true, Magnitude: Uint128{Lo: 2}}, Description: "Reverse"}
	if len(desc.Entries) != 1 || desc.Entries[0] != want {
		t.Errorf("the entry was not read back: %+v", desc.Entries)
	}
	entry["value"] = json.Number("2.5")
	_, err = parseUnresolvedValueDesc(raw, path)
	requireReplyRefusal(t, err, "reply dbc/unresolvedValueDescs/entries/value: expected number, got number")
	notANumber := map[string]any{"id": "0x100", "extended": false, "signalName": "Speed", "entries": []any{}}
	_, err = parseUnresolvedValueDesc(notANumber, path)
	requireReplyRefusal(t, err, "reply dbc/unresolvedValueDescs/id: expected number, got string")
}

// testDefinition is a one-message definition the internal tests marshal.
func testDefinition() DBCDefinition {
	sid, _ := NewStandardID(0x123)
	dlc, _ := NewDLC(8)
	return DBCDefinition{
		Version: "1.0",
		Messages: []DBCMessage{{
			ID: sid, Name: "EngineData", DLC: dlc, Sender: "ECU",
			Signals: []DBCSignal{{
				Name: "Speed", StartBit: 0, BitLength: 16, ByteOrder: LittleEndian,
				Factor:  ratOf(1, 10),
				Offset:  ratOf(0, 1),
				Minimum: ratOf(0, 1),
				Maximum: ratOf(300, 1),
				Unit:    "km/h", Presence: AlwaysPresent{},
			}},
		}},
	}
}

// definitionWire is testDefinition as the kernel's response carries it, its
// one message handed to edit first. The command form leaves a standard
// identifier's extended flag out, and the kernel writes it whatever it is.
func definitionWire(t *testing.T, edit func(msg map[string]any)) map[string]any {
	t.Helper()
	b, err := json.Marshal(testDefinition())
	if err != nil {
		t.Fatalf("marshal: %v", err)
	}
	m, err := parseResponse(string(b))
	if err != nil {
		t.Fatalf("parse: %v", err)
	}
	msg := m["messages"].([]any)[0].(map[string]any)
	msg["extended"] = false
	edit(msg)
	return m
}

// A message identifier is read at the width its flag names, whose range the
// kernel proves: either end of each width is read back, as is the largest
// number the width's field holds, and one past that or a negative one is
// refused at its place.
func TestParseDBCMessage_ReadsTheIdentifierAtItsWidth(t *testing.T) {
	cases := map[string]struct {
		id       int64
		extended bool
		ok       bool
	}{
		"standard zero":              {0, false, true},
		"largest standard":           {1<<11 - 1, false, true},
		"largest extended":           {1<<29 - 1, true, true},
		"standard field's ceiling":   {math.MaxUint16, false, true},
		"extended field's ceiling":   {math.MaxUint32, true, true},
		"past the standard field":    {math.MaxUint16 + 1, false, false},
		"past the extended field":    {math.MaxUint32 + 1, true, false},
		"negative":                   {-1, false, false},
		"negative, extended flagged": {-1, true, false},
	}
	for name, tc := range cases {
		t.Run(name, func(t *testing.T) {
			wire := definitionWire(t, func(msg map[string]any) {
				msg["id"] = json.Number(strconv.FormatInt(tc.id, 10))
				msg["extended"] = tc.extended
			})
			dbc, err := parseDBCDefinition(wire)
			if !tc.ok {
				requireReplyRefusal(t, err, "reply dbc/messages/id: expected number, got number")
				return
			}
			if err != nil {
				t.Fatalf("refused: %v", err)
			}
			id := dbc.Messages[0].ID
			if id.IsExtended() != tc.extended || int64(id.Value()) != tc.id {
				t.Errorf("read back %v, want %d (extended %v)", id, tc.id, tc.extended)
			}
		})
	}
}

// A message's length code is read from the byte count the reply writes: each
// count a code stands for is read back as that code, and a count none stands
// for is refused at its place, the largest a uint64 holds among them.
func TestParseDBCMessage_ReadsTheLengthCodeFromItsByteCount(t *testing.T) {
	for code, count := range dlcTable {
		wire := definitionWire(t, func(msg map[string]any) { msg["dlc"] = json.Number(strconv.Itoa(count)) })
		dbc, err := parseDBCDefinition(wire)
		if err != nil {
			t.Fatalf("%d bytes refused: %v", count, err)
		}
		if got := dbc.Messages[0].DLC.Value(); int(got) != code {
			t.Errorf("%d bytes read back as code %d, want %d", count, got, code)
		}
	}
	for _, count := range []string{"9", strconv.FormatUint(math.MaxUint64, 10)} {
		wire := definitionWire(t, func(msg map[string]any) { msg["dlc"] = json.Number(count) })
		_, err := parseDBCDefinition(wire)
		requireReplyRefusal(t, err, "reply dbc/messages/dlc: expected number, got number")
	}
}

// A comment's or an attribute's target identifier is read at the width its
// flag names, as the message's is, for every kind of target that carries one:
// either end is read back and a negative one is refused at its place.
func TestParseTargets_ReadTheIdentifierAtItsWidth(t *testing.T) {
	cases := map[string]struct {
		id       int64
		extended bool
		ok       bool
	}{
		"standard zero":    {0, false, true},
		"largest standard": {1<<11 - 1, false, true},
		"largest extended": {1<<29 - 1, true, true},
		"negative":         {-1, true, false},
	}
	idOf := func(target any) CANID {
		switch v := target.(type) {
		case DBCCommentTargetMessage:
			return v.ID
		case DBCCommentTargetSignal:
			return v.ID
		case DBCAttrTargetMessage:
			return v.ID
		case DBCAttrTargetSignal:
			return v.ID
		case DBCAttrTargetNodeMsg:
			return v.ID
		case DBCAttrTargetNodeSig:
			return v.ID
		}
		return nil
	}
	places := map[string]replyPath{"comment": "dbc/comments/target", "attr": "dbc/attributes/target"}
	parsers := map[string]func(map[string]any) (any, error){
		"comment": func(m map[string]any) (any, error) { return parseCommentTarget(m, places["comment"]) },
		"attr":    func(m map[string]any) (any, error) { return parseAttrTarget(m, places["attr"]) },
	}
	kinds := map[string][]string{"comment": {"message", "signal"}, "attr": {"message", "signal", "nodeMsg", "nodeSig"}}
	for parser, parse := range parsers {
		for _, kind := range kinds[parser] {
			for name, tc := range cases {
				t.Run(parser+" "+kind+" "+name, func(t *testing.T) {
					target, err := parse(map[string]any{
						"kind": kind, "id": json.Number(strconv.FormatInt(tc.id, 10)), "extended": tc.extended,
						"signal": "Speed", "node": "ECU",
					})
					if !tc.ok {
						requireReplyRefusal(t, err, "reply "+string(places[parser])+"/id: expected number, got number")
						return
					}
					if err != nil {
						t.Fatalf("refused: %v", err)
					}
					id := idOf(target)
					if id == nil || id.IsExtended() != tc.extended || int64(id.Value()) != tc.id {
						t.Errorf("read back %v, want %d (extended %v)", id, tc.id, tc.extended)
					}
				})
			}
		}
	}
}

// A fails result carries its timestamp, and an unresolved one may lack it:
// absent and null both read as none there, zero is the trace's first instant,
// and a negative or textual one is refused at its place.
func TestParsePropertyResult_ReadsTheOptionalTimestamp(t *testing.T) {
	type stamp struct {
		present bool
		us      int64
	}
	cases := map[string]struct {
		status  string
		field   string
		want    stamp
		refusal string // empty: read back as want
	}{
		"absent":         {"unresolved", ``, stamp{}, ""},
		"null":           {"unresolved", `,"timestamp":null`, stamp{}, ""},
		"zero":           {"unresolved", `,"timestamp":0`, stamp{true, 0}, ""},
		"positive":       {"unresolved", `,"timestamp":5`, stamp{true, 5}, ""},
		"negative":       {"unresolved", `,"timestamp":-1`, stamp{}, "expected number, got number"},
		"a string":       {"unresolved", `,"timestamp":"5"`, stamp{}, "expected number, got string"},
		"fails, absent":  {"fails", ``, stamp{}, "expected number, got nothing"},
		"fails, null":    {"fails", `,"timestamp":null`, stamp{}, "expected number, got null"},
		"fails, present": {"fails", `,"timestamp":5`, stamp{true, 5}, ""},
	}
	for name, tc := range cases {
		t.Run(name, func(t *testing.T) {
			r, err := parseResponse(`{"type":"property","status":"` + tc.status + `","property_index":0,"reason":"r"` + tc.field + `}`)
			if err != nil {
				t.Fatalf("parseResponse: %v", err)
			}
			pr, err := parsePropertyResult(r, "results")
			if tc.refusal != "" {
				requireReplyRefusal(t, err, "reply results/timestamp: "+tc.refusal)
				return
			}
			if err != nil {
				t.Fatalf("refused: %v", err)
			}
			var got stamp
			if pr.Timestamp != nil {
				got = stamp{true, pr.Timestamp.Microseconds}
			}
			if got != tc.want {
				t.Errorf("timestamp %+v, want %+v", got, tc.want)
			}
		})
	}
}

// A multiplexed signal's multiplexor values are whole numbers up to 2^128-1:
// either end of that range and an empty array are read back, and a value that
// is not an array, an absent one and a value that is no natural number or
// past 2^128-1 are refused at their places.
func TestParseSignalPresence_ReadsTheMultiplexValues(t *testing.T) {
	cases := map[string]struct {
		values  string
		want    []MultiplexValue
		refusal string // empty: read back as want
	}{
		"both ends":      {`,"multiplex_values":[0,340282366920938463463374607431768211455]`, []MultiplexValue{{}, {Hi: math.MaxUint64, Lo: math.MaxUint64}}, ""},
		"empty":          {`,"multiplex_values":[]`, []MultiplexValue{}, ""},
		"not an array":   {`,"multiplex_values":3`, nil, "expected array, got number"},
		"absent":         {``, nil, "expected array, got nothing"},
		"past 2^128-1":   {`,"multiplex_values":[340282366920938463463374607431768211456]`, nil, "expected number, got number"},
		"negative":       {`,"multiplex_values":[-1]`, nil, "expected number, got number"},
		"not a number":   {`,"multiplex_values":["3"]`, nil, "expected number, got string"},
		"one of two bad": {`,"multiplex_values":[1,-1]`, nil, "expected number, got number"},
	}
	for name, tc := range cases {
		t.Run(name, func(t *testing.T) {
			j, err := parseResponse(`{"presence":"multiplexed","multiplexor":"Mode"` + tc.values + `}`)
			if err != nil {
				t.Fatalf("parseResponse: %v", err)
			}
			presence, err := parseSignalPresence(j, "dbc/messages/signals")
			if tc.refusal != "" {
				requireReplyRefusal(t, err, "reply dbc/messages/signals/multiplex_values: "+tc.refusal)
				return
			}
			if err != nil {
				t.Fatalf("refused: %v", err)
			}
			got := presence.(Multiplexed)
			if got.Multiplexor != "Mode" || !slices.Equal(got.MultiplexValues, tc.want) {
				t.Errorf("read back %+v, want Mode over %v", got, tc.want)
			}
		})
	}
}

// A frame's payload bytes are read at eight bits each: either end is read
// back, and a value past either end is refused at its place.
func TestParseFrameDataResponse_ReadsEachByteAtEightBits(t *testing.T) {
	got, err := parseFrameDataResponse(`{"status":"success","data":[0,255]}`)
	if err != nil {
		t.Fatalf("refused: %v", err)
	}
	if !slices.Equal(got, FramePayload{0, 255}) {
		t.Errorf("read back %v, want [0 255]", got)
	}
	for _, data := range []string{`[256]`, `[-1]`, `[0,1,256]`} {
		_, err := parseFrameDataResponse(`{"status":"success","data":` + data + `}`)
		requireReplyRefusal(t, err, "reply data: expected number, got number")
	}
}

// The binding's own size refusal takes an input of exactly the limit and
// refuses one byte more, as the kernel's does, with the typed error the
// kernel's refusal lifts to.
func TestRefuseOversize_TakesTheLimitAndRefusesOneMore(t *testing.T) {
	const limit = 1 << 20
	if err := refuseOversize(limit, limit); err != nil {
		t.Errorf("an input of exactly the limit was refused: %v", err)
	}
	err := refuseOversize(limit+1, limit)
	var bound *InputBoundExceededError
	if !errors.As(err, &bound) {
		t.Fatalf("got %v, want an InputBoundExceededError", err)
	}
	want := InputBoundExceededError{BoundKind: BoundKindInputLengthBytes, Observed: Uint128{Lo: limit + 1}, Limit: Uint128{Lo: limit}, Code: CodeInputBoundExceeded}
	if *bound != want {
		t.Errorf("got %+v, want %+v", *bound, want)
	}
}

// A signal's start bit is read anywhere in a CAN-FD frame's 512 bits, whose
// range the kernel proves: either end is read back and a negative bit, no
// natural number, is refused at its place.
func TestParseDBCSignal_ReadsTheStartBitWithinTheLargestFrame(t *testing.T) {
	for _, tc := range []struct {
		bit int64
		ok  bool
	}{{-1, false}, {0, true}, {511, true}} {
		wire := definitionWire(t, func(msg map[string]any) {
			msg["signals"].([]any)[0].(map[string]any)["startBit"] = json.Number(strconv.FormatInt(tc.bit, 10))
		})
		dbc, err := parseDBCDefinition(wire)
		switch {
		case !tc.ok:
			requireReplyRefusal(t, err, "reply dbc/messages/signals/startBit: expected number, got number")
		case err != nil:
			t.Errorf("start bit %d refused: %v", tc.bit, err)
		case int64(dbc.Messages[0].Signals[0].StartBit) != tc.bit:
			t.Errorf("start bit %d read back as %d", tc.bit, dbc.Messages[0].Signals[0].StartBit)
		}
	}
}

// A definition built by hand can leave an identifier unset, nil in its
// interface; serializing it is a validation error naming the gap, never a
// panic, wherever the identifier sits.
func TestSerializeDBC_RefusesAnUnsetIdentifier(t *testing.T) {
	cases := map[string]func(*DBCDefinition){
		"message": func(d *DBCDefinition) { d.Messages[0].ID = nil },
		"unresolved value description": func(d *DBCDefinition) {
			d.UnresolvedValueDescriptions = []DBCRawValueDesc{{SignalName: "Speed"}}
		},
		"comment on a message": func(d *DBCDefinition) {
			d.Comments = []DBCComment{{Target: DBCCommentTargetMessage{}, Text: "x"}}
		},
		"comment on a signal": func(d *DBCDefinition) {
			d.Comments = []DBCComment{{Target: DBCCommentTargetSignal{Signal: "Speed"}, Text: "x"}}
		},
		"attribute on a message": func(d *DBCDefinition) {
			d.Attributes = []DBCAttribute{DBCAttrAssign{Name: "A", Target: DBCAttrTargetMessage{}, Value: DBCAttrValueInt{Value: 1}}}
		},
		"attribute on a signal": func(d *DBCDefinition) {
			d.Attributes = []DBCAttribute{DBCAttrAssign{Name: "A", Target: DBCAttrTargetSignal{Signal: "Speed"}, Value: DBCAttrValueInt{Value: 1}}}
		},
		"attribute on a node's message": func(d *DBCDefinition) {
			d.Attributes = []DBCAttribute{DBCAttrAssign{Name: "A", Target: DBCAttrTargetNodeMsg{Node: "ECU"}, Value: DBCAttrValueInt{Value: 1}}}
		},
		"attribute on a node's signal": func(d *DBCDefinition) {
			d.Attributes = []DBCAttribute{DBCAttrAssign{Name: "A", Target: DBCAttrTargetNodeSig{Node: "ECU", Signal: "Speed"}, Value: DBCAttrValueInt{Value: 1}}}
		},
	}
	for name, unset := range cases {
		t.Run(name, func(t *testing.T) {
			dbc := testDefinition()
			unset(&dbc)
			_, err := serializeDBC(dbc)
			requireErrorContains(t, err, "identifier is unset")
			var e *Error
			if !errors.As(err, &e) || e.Kind != ErrValidation {
				t.Errorf("got %v, want a validation error", err)
			}
		})
	}
}
