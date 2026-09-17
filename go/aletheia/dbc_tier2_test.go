// SPDX-FileCopyrightText: 2025 Nicolas Pelletier
// SPDX-License-Identifier: BSD-2-Clause

package aletheia_test

import (
	"reflect"
	"testing"

	"github.com/aletheia-automotive/aletheia-go/aletheia"
)

// tier2DBC carries every tier 2 variant: the five comment targets, the five
// attribute types, the five attribute values, the seven attribute targets
// and the three attribute records, so one round trip covers them all. The
// float bounds are rationals with no finite binary expansion.
func tier2DBC(t *testing.T) aletheia.DBCDefinition {
	t.Helper()
	return aletheia.DBCDefinition{
		Version:  "1.0",
		Messages: []aletheia.DBCMessage{minimalMessage(t, "EngineData")},
		Nodes:    []aletheia.DBCNode{{Name: "ECU"}, {Name: "Gateway"}},
		Comments: []aletheia.DBCComment{
			{Target: aletheia.DBCCommentTargetNetwork{}, Text: "network scope"},
			{Target: aletheia.DBCCommentTargetNode{Node: "ECU"}, Text: "node scope"},
			{Target: aletheia.DBCCommentTargetMessage{ID: 256}, Text: "msg scope"},
			{Target: aletheia.DBCCommentTargetSignal{ID: 256, Signal: "RPM"}, Text: "sig scope"},
			{Target: aletheia.DBCCommentTargetEnvVar{EnvVar: "AmbientTemp"}, Text: "env scope"},
		},
		Attributes: []aletheia.DBCAttribute{
			aletheia.DBCAttrDef{Name: "IntAttr", Scope: aletheia.DBCAttrScopeNetwork, AttrType: aletheia.DBCAttrTypeInt{Min: 0, Max: 100}},
			aletheia.DBCAttrDef{Name: "FloatAttr", Scope: aletheia.DBCAttrScopeSignal, AttrType: aletheia.DBCAttrTypeFloat{
				Min: aletheia.Rational{Numerator: -1, Denominator: 2}, Max: aletheia.Rational{Numerator: 22, Denominator: 7}}},
			aletheia.DBCAttrDef{Name: "StrAttr", Scope: aletheia.DBCAttrScopeMessage, AttrType: aletheia.DBCAttrTypeString{}},
			aletheia.DBCAttrDef{Name: "EnumAttr", Scope: aletheia.DBCAttrScopeNode, AttrType: aletheia.DBCAttrTypeEnum{Values: []string{"low", "high"}}},
			aletheia.DBCAttrDef{Name: "HexAttr", Scope: aletheia.DBCAttrScopeEnvVar, AttrType: aletheia.DBCAttrTypeHex{Min: 0, Max: 255}},
			aletheia.DBCAttrDefault{Name: "IntAttr", Value: aletheia.DBCAttrValueInt{Value: 42}},
			aletheia.DBCAttrAssign{Name: "IntAttr", Target: aletheia.DBCAttrTargetNetwork{}, Value: aletheia.DBCAttrValueInt{Value: 7}},
			aletheia.DBCAttrAssign{Name: "FloatAttr", Target: aletheia.DBCAttrTargetNode{Node: "ECU"},
				Value: aletheia.DBCAttrValueFloat{Value: aletheia.Rational{Numerator: 1, Denominator: 3}}},
			aletheia.DBCAttrAssign{Name: "StrAttr", Target: aletheia.DBCAttrTargetSignal{ID: 256, Signal: "RPM"}, Value: aletheia.DBCAttrValueString{Value: "hello"}},
			aletheia.DBCAttrAssign{Name: "EnumAttr", Target: aletheia.DBCAttrTargetNodeMsg{Node: "ECU", ID: 256}, Value: aletheia.DBCAttrValueEnum{Value: 1}},
			aletheia.DBCAttrAssign{Name: "HexAttr", Target: aletheia.DBCAttrTargetNodeSig{Node: "ECU", ID: 256, Signal: "RPM"}, Value: aletheia.DBCAttrValueHex{Value: 255}},
		},
	}
}

// Every tier 2 variant the serializer writes, the decoder reads back equal,
// field for field.
func TestSerializeDBC_Tier2RoundtripThroughMock(t *testing.T) {
	fixture := tier2DBC(t)
	decoded := roundTripThroughMock(t, fixture)
	if !reflect.DeepEqual(decoded.Nodes, fixture.Nodes) {
		t.Errorf("nodes: got %+v, want %+v", decoded.Nodes, fixture.Nodes)
	}
	if !reflect.DeepEqual(decoded.Comments, fixture.Comments) {
		t.Errorf("comments: got %+v, want %+v", decoded.Comments, fixture.Comments)
	}
	if !reflect.DeepEqual(decoded.Attributes, fixture.Attributes) {
		t.Errorf("attributes: got %+v, want %+v", decoded.Attributes, fixture.Attributes)
	}
}

// A signal's receivers and a message's additional senders go onto the wire
// under their keys and come back through the decoder.
func TestSignalReceiversAndMessageSenders_RoundtripThroughMock(t *testing.T) {
	dlc, _ := aletheia.BytesToDLC(8)
	speed := aletheia.DBCSignal{
		Name: "Speed", StartBit: 0, BitLength: 16, ByteOrder: aletheia.LittleEndian,
		Factor: aletheia.IntRational(1), Offset: aletheia.IntRational(0), Minimum: aletheia.IntRational(0), Maximum: aletheia.IntRational(255),
		Unit: "km/h", Presence: aletheia.AlwaysPresent{}, Receivers: []string{"ECU_A", "ECU_B"},
	}
	withReceivers := aletheia.DBCDefinition{Version: "1.0", Messages: []aletheia.DBCMessage{
		aletheia.NewDBCMessage(standardID(t, 256), "VehicleSpeed", dlc, "ECU", nil, []aletheia.DBCSignal{speed})}}
	withSenders := aletheia.DBCDefinition{Version: "1.0", Messages: []aletheia.DBCMessage{
		aletheia.NewDBCMessage(standardID(t, 256), "VehicleSpeed", dlc, "ECU_A", []string{"ECU_B", "ECU_C"}, nil)}}

	t.Run("receivers", func(t *testing.T) {
		msgs, _ := serialisedDBC(t, withReceivers)["messages"].([]any)
		sigs, _ := msgs[0].(map[string]any)["signals"].([]any)
		wire, _ := sigs[0].(map[string]any)["receivers"].([]any)
		if !reflect.DeepEqual(wire, []any{"ECU_A", "ECU_B"}) {
			t.Errorf("wire receivers: got %v", wire)
		}
		got := roundTripThroughMock(t, withReceivers).Messages[0].Signals[0].Receivers
		if !reflect.DeepEqual(got, speed.Receivers) {
			t.Errorf("decoded receivers: got %v, want %v", got, speed.Receivers)
		}
	})
	t.Run("senders", func(t *testing.T) {
		msgs, _ := serialisedDBC(t, withSenders)["messages"].([]any)
		wire, _ := msgs[0].(map[string]any)["senders"].([]any)
		if !reflect.DeepEqual(wire, []any{"ECU_B", "ECU_C"}) {
			t.Errorf("wire senders: got %v", wire)
		}
		got := roundTripThroughMock(t, withSenders).Messages[0].Senders
		if !reflect.DeepEqual(got, []string{"ECU_B", "ECU_C"}) {
			t.Errorf("decoded senders: got %v", got)
		}
	})
}

// Tier 2 keys, a signal's receivers and a message's senders absent from a
// response decode to nil.
func TestFormatDBC_AbsentTier2KeysDecodeToNil(t *testing.T) {
	c, _ := mockClient(t, aletheia.Respond(formatDBCResponse(oneSignalMessage(
		`{"name":"S","startBit":0,"length":8,"byteOrder":"little_endian","signed":false,"factor":1,"offset":0,"minimum":0,"maximum":255,"unit":"","presence":"always"}`))))
	dbc, err := c.FormatDBC(ctx)
	if err != nil {
		t.Fatalf("FormatDBC: %v", err)
	}
	if dbc.Nodes != nil || dbc.Comments != nil || dbc.Attributes != nil {
		t.Errorf("expected nil tier 2 slices, got %v %v %v", dbc.Nodes, dbc.Comments, dbc.Attributes)
	}
	if got := dbc.Messages[0].Senders; got != nil {
		t.Errorf("absent senders: want nil, got %v", got)
	}
	if got := dbc.Messages[0].Signals[0].Receivers; got != nil {
		t.Errorf("absent receivers: want nil, got %v", got)
	}
}

// A comment target kind outside the five is a protocol error naming it.
func TestFormatDBC_RejectsUnknownCommentTargetKind(t *testing.T) {
	c, _ := mockClient(t, aletheia.Respond(`{"status":"success","dbc":{"version":"0.1","messages":[],"comments":[{"target":{"kind":"bogus"},"text":"bad"}]}}`))
	_, err := c.FormatDBC(ctx)
	requireKind(t, err, aletheia.ErrProtocol)
	requireErrorContains(t, err, "comment target kind")
}

// Absent tier 2 metadata is written as three empty arrays.
func TestSerializeDBC_EmitsEmptyTier2ArraysWhenMetadataAbsent(t *testing.T) {
	dbcObj := serialisedDBC(t, aletheia.DBCDefinition{Version: "1.0", Messages: []aletheia.DBCMessage{minimalMessage(t, "MinimalMsg")}})
	for _, key := range []string{"nodes", "comments", "attributes"} {
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
