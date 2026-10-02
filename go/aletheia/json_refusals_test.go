// SPDX-FileCopyrightText: 2025 Nicolas Pelletier
// SPDX-License-Identifier: BSD-2-Clause

package aletheia

import (
	"encoding/json"
	"errors"
	"fmt"
	"slices"
	"strconv"
	"strings"
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

// An unresolved value description whose identifier is out of its width's
// range is refused at the parse, for either width.
func TestParseUnresolvedValueDescs_RefusesAnIdentifierOutOfRange(t *testing.T) {
	cases := map[string]struct {
		id       int64
		extended bool
		want     string
	}{
		"extended past 29 bits": {1 << 29, true, "29-bit"},
		"standard past 11 bits": {1 << 11, false, "11-bit"},
	}
	for name, tc := range cases {
		t.Run(name, func(t *testing.T) {
			raw := map[string]any{"unresolvedValueDescs": []any{map[string]any{
				"id": json.Number(strconv.FormatInt(tc.id, 10)), "extended": tc.extended, "signalName": "Speed", "entries": []any{},
			}}}
			_, err := parseUnresolvedValueDescs(raw)
			if err == nil || !strings.Contains(err.Error(), tc.want) {
				t.Errorf("got %v, want an error naming the %s range", err, tc.want)
			}
		})
	}
	entry := map[string]any{"value": json.Number("2"), "description": "Reverse"}
	raw := map[string]any{"unresolvedValueDescs": []any{map[string]any{
		"id": json.Number(strconv.Itoa(1<<29 - 1)), "extended": true, "signalName": "Speed", "entries": []any{entry},
	}}}
	descs, err := parseUnresolvedValueDescs(raw)
	if err != nil || len(descs) != 1 || !descs[0].ID.IsExtended() || descs[0].ID.Value() != 1<<29-1 {
		t.Fatalf("the largest extended identifier was not read back: %v, %v", descs, err)
	}
	if len(descs[0].Entries) != 1 || descs[0].Entries[0].Value != 2 || descs[0].Entries[0].Description != "Reverse" {
		t.Errorf("the entry was not read back: %+v", descs[0].Entries)
	}
	entry["value"] = json.Number("2.5")
	if _, err := parseUnresolvedValueDescs(raw); err == nil || !strings.Contains(err.Error(), "entry value") {
		t.Errorf("a fractional entry value was not refused: %v", err)
	}
	notANumber := map[string]any{"unresolvedValueDescs": []any{map[string]any{"id": "0x100", "signalName": "Speed"}}}
	if _, err := parseUnresolvedValueDescs(notANumber); err == nil || !strings.Contains(err.Error(), "unresolvedValueDesc id") {
		t.Errorf("an identifier that is not a number was not refused: %v", err)
	}
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
				Factor:  Rational{Numerator: 1, Denominator: 10},
				Offset:  Rational{Numerator: 0, Denominator: 1},
				Minimum: Rational{Numerator: 0, Denominator: 1},
				Maximum: Rational{Numerator: 300, Denominator: 1},
				Unit:    "km/h", Presence: AlwaysPresent{},
			}},
		}},
	}
}

// definitionWire is testDefinition as the kernel's response carries it, its
// one message handed to edit first.
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
	edit(m["messages"].([]any)[0].(map[string]any))
	return m
}

// A message identifier is read at the width its flag names: one past that
// width is refused rather than truncated into range, and either end of the
// range is read back.
func TestParseDBCMessage_ReadsTheIdentifierAtItsWidth(t *testing.T) {
	cases := map[string]struct {
		id       int64
		extended bool
		want     string // empty: read back as id
	}{
		"standard zero":              {0, false, ""},
		"largest standard":           {1<<11 - 1, false, ""},
		"standard past 11 bits":      {1 << 11, false, "11-bit"},
		"standard past 16 bits":      {1<<16 + 5, false, "standard id out of range"},
		"largest extended":           {1<<29 - 1, true, ""},
		"extended past 29 bits":      {1 << 29, true, "29-bit"},
		"extended past 32 bits":      {1<<32 + 5, true, "out of uint32 range"},
		"negative":                   {-1, false, "out of uint32 range"},
		"negative, extended flagged": {-1, true, "out of uint32 range"},
	}
	for name, tc := range cases {
		t.Run(name, func(t *testing.T) {
			wire := definitionWire(t, func(msg map[string]any) {
				msg["id"] = json.Number(strconv.FormatInt(tc.id, 10))
				msg["extended"] = tc.extended
			})
			dbc, err := parseDBCDefinition(wire)
			if tc.want != "" {
				if err == nil || !strings.Contains(err.Error(), tc.want) {
					t.Fatalf("got %v, %v; want an error containing %q", dbc, err, tc.want)
				}
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

// An unresolved value description's standard identifier past sixteen bits is
// refused, as the message's is, rather than read as its low sixteen bits.
func TestParseUnresolvedValueDescs_RefusesAStandardIdentifierPastSixteenBits(t *testing.T) {
	raw := map[string]any{"unresolvedValueDescs": []any{map[string]any{
		"id": json.Number(strconv.Itoa(1<<16 + 5)), "extended": false, "signalName": "Speed", "entries": []any{},
	}}}
	if descs, err := parseUnresolvedValueDescs(raw); err == nil {
		t.Errorf("read back %v, want a refusal", descs)
	}
}

// A comment's or an attribute's target identifier is read at the width its
// flag names, as the message's is, for every kind of target that carries one.
func TestParseTargets_ReadTheIdentifierAtItsWidth(t *testing.T) {
	cases := map[string]struct {
		id       int64
		extended bool
		ok       bool
	}{
		"standard zero":         {0, false, true},
		"standard past 11 bits": {1 << 11, false, false},
		"standard past 16 bits": {1<<16 + 5, false, false},
		"largest extended":      {1<<29 - 1, true, true},
		"largest wire value":    {1<<32 - 1, true, false},
		"past the wire value":   {1 << 32, true, false},
		"negative":              {-1, true, false},
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
	parsers := map[string]func(map[string]any) (any, error){
		"comment": func(m map[string]any) (any, error) { return parseCommentTarget(m) },
		"attr":    func(m map[string]any) (any, error) { return parseAttrTarget(m) },
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
						if err == nil {
							t.Fatalf("read back %v, want a refusal", target)
						}
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

// A result's timestamp is optional: absent and null both read as none, zero
// is the trace's first instant, and a negative one is refused.
func TestParsePropertyResult_ReadsTheOptionalTimestamp(t *testing.T) {
	type stamp struct {
		present bool
		us      int64
	}
	cases := map[string]struct {
		field string
		want  stamp
		ok    bool
	}{
		"absent":   {``, stamp{}, true},
		"null":     {`,"timestamp":null`, stamp{}, true},
		"zero":     {`,"timestamp":0`, stamp{true, 0}, true},
		"positive": {`,"timestamp":5`, stamp{true, 5}, true},
		"negative": {`,"timestamp":-1`, stamp{}, false},
		"a string": {`,"timestamp":"5"`, stamp{}, false},
	}
	for name, tc := range cases {
		t.Run(name, func(t *testing.T) {
			r, err := parseResponse(`{"status":"fails","property_index":0` + tc.field + `}`)
			if err != nil {
				t.Fatalf("parseResponse: %v", err)
			}
			pr, err := parsePropertyResult(r)
			if !tc.ok {
				if err == nil {
					t.Fatalf("read back %+v, want a refusal", pr)
				}
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

// A multiplexed signal carries at least one multiplexor value, each read at
// the thirty-two bits the wire gives it: either end of that range is read
// back, and an empty array, a value that is not an array, an absent one and a
// value past either end are refused.
func TestParseSignalPresence_ReadsTheMultiplexValues(t *testing.T) {
	cases := map[string]struct {
		values string
		want   []MultiplexValue // nil: refused
	}{
		"both ends":      {`,"multiplex_values":[0,4294967295]`, []MultiplexValue{0, 1<<32 - 1}},
		"empty":          {`,"multiplex_values":[]`, nil},
		"not an array":   {`,"multiplex_values":3`, nil},
		"absent":         {``, nil},
		"past 32 bits":   {`,"multiplex_values":[4294967296]`, nil},
		"negative":       {`,"multiplex_values":[-1]`, nil},
		"not a number":   {`,"multiplex_values":["3"]`, nil},
		"one of two bad": {`,"multiplex_values":[1,4294967296]`, nil},
	}
	for name, tc := range cases {
		t.Run(name, func(t *testing.T) {
			j, err := parseResponse(`{"presence":"multiplexed","multiplexor":"Mode"` + tc.values + `}`)
			if err != nil {
				t.Fatalf("parseResponse: %v", err)
			}
			presence, err := parseSignalPresence(j)
			if tc.want == nil {
				if err == nil {
					t.Fatalf("read back %+v, want a refusal", presence)
				}
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
// back, and a value past either end is refused.
func TestParseFrameDataResponse_ReadsEachByteAtEightBits(t *testing.T) {
	got, err := parseFrameDataResponse(`{"status":"success","data":[0,255]}`)
	if err != nil {
		t.Fatalf("refused: %v", err)
	}
	if !slices.Equal(got, FramePayload{0, 255}) {
		t.Errorf("read back %v, want [0 255]", got)
	}
	for _, data := range []string{`[256]`, `[-1]`, `[0,1,256]`} {
		if got, err := parseFrameDataResponse(`{"status":"success","data":` + data + `}`); err == nil {
			t.Errorf("%s read back as %v, want a refusal", data, got)
		}
	}
}

// The checked narrowing answers the value and true exactly when the target
// type holds it, at both ends of each type the package narrows into.
func TestNarrow_HoldsExactlyTheValuesTheTypeCarries(t *testing.T) {
	check := func(name string, ok, wantOK bool) {
		t.Helper()
		if ok != wantOK {
			t.Errorf("%s: ok = %v, want %v", name, ok, wantOK)
		}
	}
	for _, tc := range []struct {
		v  int64
		ok bool
	}{{-1, false}, {0, true}, {255, true}, {256, false}} {
		got, ok := narrow[uint8](tc.v)
		check(fmt.Sprintf("uint8 %d", tc.v), ok, tc.ok)
		if ok && int64(got) != tc.v {
			t.Errorf("uint8 %d came back as %d", tc.v, got)
		}
	}
	for _, tc := range []struct {
		v  int64
		ok bool
	}{{-1, false}, {0, true}, {1<<16 - 1, true}, {1 << 16, false}} {
		got, ok := narrow[uint16](tc.v)
		check(fmt.Sprintf("uint16 %d", tc.v), ok, tc.ok)
		if ok && int64(got) != tc.v {
			t.Errorf("uint16 %d came back as %d", tc.v, got)
		}
	}
	for _, tc := range []struct {
		v  int64
		ok bool
	}{{-1, false}, {0, true}, {1<<32 - 1, true}, {1 << 32, false}} {
		got, ok := narrow[uint32](tc.v)
		check(fmt.Sprintf("uint32 %d", tc.v), ok, tc.ok)
		if ok && int64(got) != tc.v {
			t.Errorf("uint32 %d came back as %d", tc.v, got)
		}
	}
	for _, tc := range []struct {
		v  int64
		ok bool
	}{{-1<<31 - 1, false}, {-1 << 31, true}, {0, true}, {1<<31 - 1, true}, {1 << 31, false}} {
		got, ok := narrow[int32](tc.v)
		check(fmt.Sprintf("int32 %d", tc.v), ok, tc.ok)
		if ok && int64(got) != tc.v {
			t.Errorf("int32 %d came back as %d", tc.v, got)
		}
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
	want := InputBoundExceededError{BoundKind: BoundKindInputLengthBytes, Observed: limit + 1, Limit: limit, Code: CodeInputBoundExceeded}
	if *bound != want {
		t.Errorf("got %+v, want %+v", *bound, want)
	}
}

// A signal's start bit is read anywhere in a CAN-FD frame's 512 bits: either
// end is read back and a bit past either end is refused.
func TestParseDBCSignal_ReadsTheStartBitWithinTheLargestFrame(t *testing.T) {
	for _, tc := range []struct {
		bit int64
		ok  bool
	}{{-1, false}, {0, true}, {511, true}, {512, false}} {
		wire := definitionWire(t, func(msg map[string]any) {
			msg["signals"].([]any)[0].(map[string]any)["startBit"] = json.Number(strconv.FormatInt(tc.bit, 10))
		})
		dbc, err := parseDBCDefinition(wire)
		switch {
		case !tc.ok && err == nil:
			t.Errorf("start bit %d read back, want a refusal", tc.bit)
		case tc.ok && err != nil:
			t.Errorf("start bit %d refused: %v", tc.bit, err)
		case tc.ok && int64(dbc.Messages[0].Signals[0].StartBit) != tc.bit:
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
