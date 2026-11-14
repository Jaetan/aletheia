// SPDX-FileCopyrightText: 2025 Nicolas Pelletier
// SPDX-License-Identifier: BSD-2-Clause

package aletheia

import (
	"reflect"
	"slices"
	"strings"
	"testing"
)

// dbcWordPlace is a DBC place the reply proof holds to a set of words: the
// object holding it, read by read from path, its key, the other members every
// word's arm reads and those one word's arm alone reads, its words as a
// refusal quotes them, and each word with the value it is read as.
type dbcWordPlace struct {
	path     replyPath
	key      string
	others   []string
	armOnly  map[string][]string
	expected string
	read     func(map[string]any, replyPath) (any, error)
	words    []dbcWordRead
}

// dbcWordRead is a word of a place and the value it is read as.
type dbcWordRead struct {
	word string
	want any
}

// readWord reads the place's object holding value, a JSON text, at its key,
// or holding no key when value is empty, beside the place's other members and
// the members more holds.
func (p dbcWordPlace) readWord(t *testing.T, value string, more ...string) (any, error) {
	t.Helper()
	members := append(slices.Clone(p.others), more...)
	if value != "" {
		members = append([]string{`"` + p.key + `":` + value}, members...)
	}
	j, err := parseResponse("{" + strings.Join(members, ",") + "}")
	if err != nil {
		t.Fatalf("parseResponse: %v", err)
	}
	return p.read(j, p.path)
}

// dbcWordPlaces are the DBC places a reply holds to a set of words.
var dbcWordPlaces = []dbcWordPlace{
	{
		path: "dbc/messages/signals", key: "byteOrder",
		expected: `"little_endian" or "big_endian"`,
		read: func(j map[string]any, path replyPath) (any, error) {
			return readByteOrder(j, path)
		},
		words: []dbcWordRead{{"little_endian", LittleEndian}, {"big_endian", BigEndian}},
	},
	{
		path: "dbc/messages/signals", key: "presence",
		others:   []string{`"multiplexor":"Mode"`, `"multiplex_values":[1]`},
		expected: `"always" or "multiplexed"`,
		read: func(j map[string]any, path replyPath) (any, error) {
			return parseSignalPresence(j, path)
		},
		words: []dbcWordRead{
			{"always", AlwaysPresent{}},
			{"multiplexed", Multiplexed{Multiplexor: "Mode", MultiplexValues: []MultiplexValue{{Lo: 1}}}},
		},
	},
	{
		path: "dbc/comments/target", key: "kind",
		others:   []string{`"node":"N"`, `"id":5`, `"extended":false`, `"signal":"S"`, `"envVar":"E"`},
		expected: `"network", "node", "message", "signal" or "envVar"`,
		read: func(j map[string]any, path replyPath) (any, error) {
			return parseCommentTarget(j, path)
		},
		words: []dbcWordRead{
			{"network", DBCCommentTargetNetwork{}},
			{"node", DBCCommentTargetNode{Node: "N"}},
			{"message", DBCCommentTargetMessage{ID: StandardID{value: 5}}},
			{"signal", DBCCommentTargetSignal{ID: StandardID{value: 5}, Signal: "S"}},
			{"envVar", DBCCommentTargetEnvVar{EnvVar: "E"}},
		},
	},
	{
		path: "dbc/attributes", key: "kind",
		others: []string{
			`"name":"A"`, `"scope":"network"`, `"attrType":{"kind":"string"}`,
			`"value":{"kind":"string","value":"v"}`, `"target":{"kind":"network"}`,
		},
		expected: `"definition", "default" or "assignment"`,
		read: func(j map[string]any, path replyPath) (any, error) {
			return parseAttribute(j, path)
		},
		words: []dbcWordRead{
			{"definition", DBCAttrDef{Name: "A", Scope: DBCAttrScopeNetwork, AttrType: DBCAttrTypeString{}}},
			{"default", DBCAttrDefault{Name: "A", Value: DBCAttrValueString{Value: "v"}}},
			{"assignment", DBCAttrAssign{Name: "A", Target: DBCAttrTargetNetwork{}, Value: DBCAttrValueString{Value: "v"}}},
		},
	},
	{
		path: "dbc/attributes", key: "scope",
		expected: `"network", "node", "message", "signal", "envVar", "nodeMsg" or "nodeSig"`,
		read: func(j map[string]any, path replyPath) (any, error) {
			return readAttrScope(j, path)
		},
		words: []dbcWordRead{
			{"network", DBCAttrScopeNetwork},
			{"node", DBCAttrScopeNode},
			{"message", DBCAttrScopeMessage},
			{"signal", DBCAttrScopeSignal},
			{"envVar", DBCAttrScopeEnvVar},
			{"nodeMsg", DBCAttrScopeNodeMsg},
			{"nodeSig", DBCAttrScopeNodeSig},
		},
	},
	{
		path: "dbc/attributes/attrType", key: "kind",
		others:   []string{`"min":0`, `"max":7`, `"values":["a"]`},
		expected: `"int", "float", "string", "enum" or "hex"`,
		read: func(j map[string]any, path replyPath) (any, error) {
			return parseAttrType(j, path)
		},
		words: []dbcWordRead{
			{"int", DBCAttrTypeInt{Min: 0, Max: 7}},
			{"float", DBCAttrTypeFloat{
				Min: Rational{Denominator: Uint128{Lo: 1}},
				Max: Rational{Numerator: Uint128{Lo: 7}, Denominator: Uint128{Lo: 1}},
			}},
			{"string", DBCAttrTypeString{}},
			{"enum", DBCAttrTypeEnum{Values: []string{"a"}}},
			{"hex", DBCAttrTypeHex{Min: 0, Max: 7}},
		},
	},
	{
		path: "dbc/attributes/value", key: "kind",
		armOnly: map[string][]string{
			"int": {`"value":7`}, "float": {`"value":7`}, "string": {`"value":"v"`},
			"enum": {`"value":7`}, "hex": {`"value":7`},
		},
		expected: `"int", "float", "string", "enum" or "hex"`,
		read: func(j map[string]any, path replyPath) (any, error) {
			return parseAttrValue(j, path)
		},
		words: []dbcWordRead{
			{"int", DBCAttrValueInt{Value: 7}},
			{"float", DBCAttrValueFloat{Value: Rational{Numerator: Uint128{Lo: 7}, Denominator: Uint128{Lo: 1}}}},
			{"string", DBCAttrValueString{Value: "v"}},
			{"enum", DBCAttrValueEnum{Value: 7}},
			{"hex", DBCAttrValueHex{Value: 7}},
		},
	},
	{
		path: "dbc/attributes/target", key: "kind",
		others:   []string{`"node":"N"`, `"id":5`, `"extended":false`, `"signal":"S"`, `"envVar":"E"`},
		expected: `"network", "node", "message", "signal", "envVar", "nodeMsg" or "nodeSig"`,
		read: func(j map[string]any, path replyPath) (any, error) {
			return parseAttrTarget(j, path)
		},
		words: []dbcWordRead{
			{"network", DBCAttrTargetNetwork{}},
			{"node", DBCAttrTargetNode{Node: "N"}},
			{"message", DBCAttrTargetMessage{ID: StandardID{value: 5}}},
			{"signal", DBCAttrTargetSignal{ID: StandardID{value: 5}, Signal: "S"}},
			{"envVar", DBCAttrTargetEnvVar{EnvVar: "E"}},
			{"nodeMsg", DBCAttrTargetNodeMsg{Node: "N", ID: StandardID{value: 5}}},
			{"nodeSig", DBCAttrTargetNodeSig{Node: "N", ID: StandardID{value: 5}, Signal: "S"}},
		},
	},
}

// Each word of a DBC place is read as its value.
func TestDBCWord_EachWordOfItsPlaceIsReadAsItsValue(t *testing.T) {
	for _, place := range dbcWordPlaces {
		t.Run(string(place.path.at(place.key)), func(t *testing.T) {
			for _, w := range place.words {
				got, err := place.readWord(t, quoteJSON(w.word), place.armOnly[w.word]...)
				if err != nil {
					t.Errorf("%s: %v, want it read", w.word, err)
					continue
				}
				if !reflect.DeepEqual(got, w.want) {
					t.Errorf("%s: read as %#v, want %#v", w.word, got, w.want)
				}
			}
		})
	}
}

// A DBC place's word outside its words is refused at its place, a word as well
// as nothing or a number.
func TestDBCWord_OutsideItsPlaceWordsIsRefusedAtItsPlace(t *testing.T) {
	for _, place := range dbcWordPlaces {
		t.Run(string(place.path.at(place.key)), func(t *testing.T) {
			requireRowsRefused(t, func(t *testing.T, value string) error {
				_, err := place.readWord(t, value)
				return err
			}, string(place.path.at(place.key)), place.expected, []refusedRow{
				{`"bogus_word"`, `"bogus_word"`},
				{"", "nothing"},
				{"0", "number"},
			})
		})
	}
}
