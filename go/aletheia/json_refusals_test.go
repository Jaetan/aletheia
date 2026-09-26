// SPDX-FileCopyrightText: 2025 Nicolas Pelletier
// SPDX-License-Identifier: BSD-2-Clause

package aletheia

import (
	"encoding/json"
	"errors"
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
