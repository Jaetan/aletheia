// SPDX-FileCopyrightText: 2025 Nicolas Pelletier
// SPDX-License-Identifier: BSD-2-Clause

// The fuzz targets, one for each parser or serializer the binding owns:
// serializeCommand, parseResponse, parseExtractionBin, parseRational and
// parseDBCDefinition, under the five names the binding's standard pins. Each
// seeds a small corpus with f.Add and asserts that no input panics, which is
// what these exist for; the ordinary tests cover what the parsers accept and
// refuse.
//
// The seeds are inline. The standard also expects a corpus under
// testdata/fuzz per target, which the tree does not carry, so a crash found
// and minimised is committed there beside the fix it guards.
//
//	go test -fuzz=FuzzParseResponse -fuzztime=60s ./aletheia/  // one target
//	go test ./aletheia/                                        // every seed, no fuzzing

package aletheia

import (
	"encoding/json"
	"testing"
)

// The response envelope parser answers a map or a typed error, never a panic,
// whatever the bytes: invalid UTF-8, oversized numbers, deep nesting, NUL
// bytes, control characters.
func FuzzParseResponse(f *testing.F) {
	f.Add(`{"status":"ack"}`)
	f.Add(`{"status":"error","code":"x","message":"y"}`)
	f.Add(`{"status":"validation","has_errors":false,"issues":[]}`)
	f.Add(`{}`)
	f.Add(``)
	f.Add(`{"deeply":{"nested":{"map":{"value":42}}}}`)

	f.Fuzz(func(t *testing.T, raw string) {
		_, _ = parseResponse(raw)
	})
}

// What the command serializer emits, the response parser reads back, and the
// command survives the trip. A serializer and a parser that disagree are a
// binding that cannot talk to itself, and the command is the field the
// kernel dispatches on, so a value altered in transit is a command sent
// elsewhere.
func FuzzMarshalCommand(f *testing.F) {
	f.Add("parseDBC", "field1", "value1")
	f.Add("setProperties", "properties", "[]")
	f.Add("validateDBC", "dbc", `{"messages":[]}`)
	f.Add("", "", "")

	f.Fuzz(func(t *testing.T, command, key, value string) {
		out, err := serializeCommand(command, map[string]any{key: value})
		if err != nil {
			return // a refusal is an answer; the property is about what it emits
		}
		parsed, perr := parseResponse(out)
		if perr != nil {
			t.Errorf("serializeCommand produced unparseable output: %q (%v)", out, perr)
		}
		if got := parsed["command"]; got != command {
			t.Errorf("command round-trip: want %q, got %q", command, got)
		}
	})
}

// The binary extraction decoder answers or refuses, never panics, whatever
// the bytes: a short read, a size that does not match the header, an index
// past the names, a denominator of zero, an offsets table that breaks one of
// its invariants, a reason slice that is not UTF-8.
func FuzzDecodeBinaryFrame(f *testing.F) {
	f.Add([]byte{0, 0, 0, 0, 0, 0, 0, 0}, "Speed,RPM,Temp")
	f.Add([]byte{}, "")
	f.Add([]byte{0xFF, 0xFF, 0xFF, 0xFF}, "X")
	f.Add(make([]byte, 256), "A,B,C,D,E,F,G,H")
	f.Add(binExtractionValue(1, 3), "Sig")                          // one value, empty offsets table
	f.Add(binExtractionErrors([]string{"boom", "näh"}, nil), "Sig") // two errors with reasons
	f.Add(binExtractionErrors([]string{"x"}, []uint32{0, 2}), "S")  // offsets end past the reason bytes

	f.Fuzz(func(t *testing.T, buf []byte, csvNames string) {
		var names []string
		if csvNames != "" {
			names = []string{csvNames} // one signal name per run
		}
		_, _ = parseExtractionBin(buf, names)
	})
}

// The wire rational parser takes every JSON value without panicking, the
// integer shape and the numerator-denominator object alike, a zero
// denominator among them.
func FuzzParseRationalNumber(f *testing.F) {
	f.Add(`42`)
	f.Add(`{"numerator":3,"denominator":7}`)
	f.Add(`{"numerator":0,"denominator":1}`)
	f.Add(`{"numerator":-100,"denominator":3}`)
	f.Add(`null`)
	f.Add(`{"numerator":1,"denominator":0}`)
	f.Add(``)

	f.Fuzz(func(t *testing.T, raw string) {
		var v any
		if err := json.Unmarshal([]byte(raw), &v); err != nil {
			return // not JSON, so not this parser's to answer for
		}
		_, _ = parseRational(v)
	})
}

// The DBC shape parser takes every JSON object without panicking: a missing
// field, a string where a number belongs, a byte order or presence outside
// the enumeration, a nested rational that is malformed.
func FuzzParseDBCJSON(f *testing.F) {
	f.Add(`{"messages":[]}`)
	f.Add(`{"messages":[{"id":256,"name":"M","dlc":8,"sender":"E","signals":[]}]}`)
	f.Add(`{"messages":[{"id":256,"name":"","dlc":8,"sender":"","signals":[]}]}`)
	f.Add(``)
	f.Add(`null`)
	f.Add(`{"messages":null}`)

	f.Fuzz(func(t *testing.T, raw string) {
		var j map[string]any
		if err := json.Unmarshal([]byte(raw), &j); err != nil {
			return // not JSON, so not this parser's to answer for
		}
		_, _ = parseDBCDefinition(j)
	})
}
