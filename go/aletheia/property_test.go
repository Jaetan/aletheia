// SPDX-FileCopyrightText: 2025 Nicolas Pelletier
// SPDX-License-Identifier: BSD-2-Clause

// Properties over generated inputs, one check each. They sit beside the fuzz
// targets and answer a different question: a fuzzer finds the input that
// crashes, a property finds the input that comes back wrong. The binding's
// standard asks for both, and for a round trip over every wire shape the
// binding encodes.

package aletheia

import (
	"encoding/json"
	"strconv"
	"testing"
	"testing/quick"
)

// A rational encoded and read back is the same value, for any numerator and
// any denominator above zero. The trip goes through the decoder the library
// uses, so what is under test is the wire and not a pair of helpers. The
// values past what a float holds are pinned separately, by
// TestParseResponse_ExactLargeRational.
func TestProperty_RationalRoundTrip(t *testing.T) {
	property := func(num int32, denomNonZero uint16) bool {
		denom := int64(denomNonZero) + 1
		original := Rational{Numerator: int64(num), Denominator: denom}
		// Wrap in a one-field object and decode via the real wire decoder.
		bytes, mErr := json.Marshal(map[string]any{"value": serializeRational(original)})
		if mErr != nil {
			return true // marshal failure is acceptable; parseRational not reached
		}
		m, pErr := parseResponse(string(bytes))
		if pErr != nil {
			t.Logf("parseResponse(%s) failed: %v", bytes, pErr)
			return false
		}
		parsed, err := parseRational(m["value"])
		if err != nil {
			t.Logf("parseRational(%v) failed: %v", m["value"], err)
			return false
		}
		// The decoder may return another pair of the same value, so the two
		// are compared by cross-multiplication rather than by their fields.
		return original.Numerator*parsed.Denominator == parsed.Numerator*original.Denominator
	}
	if err := quick.Check(property, &quick.Config{MaxCount: 200}); err != nil {
		t.Errorf("RationalRoundTrip property failed: %v", err)
	}
}

// The response parser answers for every input rather than panicking on one.
// The bytes here are forced into the printable range, which is the shape a
// wire error takes; the fuzz target covers arbitrary bytes.
func TestProperty_ParseResponseTotal(t *testing.T) {
	property := func(payload []byte) bool {
		ascii := make([]byte, len(payload))
		for i, b := range payload {
			ascii[i] = (b & 0x7F) | 0x20 // printable range
		}
		_, _ = parseResponse(string(ascii))
		return true // reaching here is the claim: the call returned
	}
	if err := quick.Check(property, &quick.Config{MaxCount: 200}); err != nil {
		t.Errorf("ParseResponseTotal property failed: %v", err)
	}
}

// A command encoded and read back names the same command, for any command
// and any field name. An input the encoder refuses, such as one that is not
// valid UTF-8, is not a counterexample: it never reached the wire.
func TestProperty_CommandRoundTrip(t *testing.T) {
	property := func(command, key string) bool {
		fields := map[string]any{key: "v"}
		out, err := serializeCommand(command, fields)
		if err != nil {
			return true // marshal error is acceptable for adversarial input
		}
		parsed, err := parseResponse(out)
		if err != nil {
			t.Logf("parseResponse(%q) failed after serializeCommand: %v", out, err)
			return false
		}
		got, ok := parsed["command"].(string)
		if !ok {
			return false
		}
		return got == command
	}
	if err := quick.Check(property, &quick.Config{MaxCount: 200}); err != nil {
		t.Errorf("CommandRoundTrip property failed: %v", err)
	}
}

// Reading two numbers off the wire keeps their order, strictly. The
// comparison is exact: both come back over a denominator of one, so their
// numerators are the values themselves, and putting them through a float
// would lose the distinction this property exists to find.
func TestProperty_RationalOrderIsPreserved(t *testing.T) {
	property := func(a, b int64) bool {
		if a == b {
			return true
		}
		ra, errA := parseRational(json.Number(strconv.FormatInt(a, 10)))
		rb, errB := parseRational(json.Number(strconv.FormatInt(b, 10)))
		if errA != nil || errB != nil {
			return true // a number the wire refuses is not a counterexample
		}
		if ra.Denominator != 1 || rb.Denominator != 1 {
			return false // an integer is the rational over one
		}
		if a < b {
			return ra.Numerator < rb.Numerator
		}
		return ra.Numerator > rb.Numerator
	}
	if err := quick.Check(property, &quick.Config{MaxCount: 200}); err != nil {
		t.Errorf("the order of two numbers was not preserved: %v", err)
	}
}

// What the wire refuses, rather than what it carries, is held over the same
// decoder by TestNumericReaders_AcceptAndRefuseTheSameShapes in
// json_precision_test.go, which feeds each shape as the bytes a response
// would carry.

// Every response shape a test can queue is one the parser reads and finds a
// status in. A mock that could produce a shape the decoders refuse would make
// every test on it a test of something the library never emits.
func TestMockResponseShapes_Decode(t *testing.T) {
	cannedResponses := []string{
		`{"status":"ack"}`,
		`{"status":"success"}`,
		`{"status":"validation","has_errors":false,"issues":[]}`,
		`{"status":"error","code":"x","message":"y"}`,
		`{"status":"fails","type":"property","property_index":{"numerator":0,"denominator":1},"timestamp":{"numerator":1000,"denominator":1}}`,
	}
	for _, raw := range cannedResponses {
		m, err := parseResponse(raw)
		if err != nil {
			t.Errorf("parseResponse(%q): %v", raw, err)
			continue
		}
		if _, hasStatus := m["status"]; !hasStatus {
			t.Errorf("parseResponse(%q) found no status", raw)
		}
	}
}

// A definition encoded, sent to the kernel and read back is the definition
// that was sent, for any signal the format allows. This is the round trip the
// binding's standard asks for over the shapes it encodes, and it goes through
// the library rather than through a canned answer: a mock would return what
// the test wrote and hold nothing.
func TestProperty_DefinitionRoundTripsThroughTheKernel(t *testing.T) {
	lib := findFFILibrary()
	if lib == "" {
		t.Skip("libaletheia-ffi.so not found; run 'cabal run shake -- build' first")
	}
	backend, err := NewFFIBackend(lib)
	if err != nil {
		t.Skipf("the library is present but would not open: %v", err)
	}
	c, err := NewClient(backend)
	if err != nil {
		t.Fatalf("NewClient: %v", err)
	}
	defer func() { _ = c.Close() }()

	property := func(rawStart uint8, rawLength uint8, rawFactor uint16, rawOffset int16) bool {
		// The generated numbers are brought into the ranges the format has,
		// so that what is under test is the trip and not the validator.
		length := BitLength(rawLength%16 + 1)
		start := BitPosition(uint16(rawStart) % uint16(64-length+1))
		factor := Rational{Numerator: int64(rawFactor%1000 + 1), Denominator: 1000}
		offset := Rational{Numerator: int64(rawOffset), Denominator: 1}
		sid, err := NewStandardID(0x123)
		if err != nil {
			return false
		}
		dlc, err := NewDLC(8)
		if err != nil {
			return false
		}
		sent := DBCDefinition{
			Version: "1.0",
			Messages: []DBCMessage{{
				ID: sid, Name: "Msg", DLC: dlc, Sender: "ECU",
				Signals: []DBCSignal{{
					Name: "Sig", StartBit: start, BitLength: length,
					ByteOrder: LittleEndian,
					Factor:    factor, Offset: offset,
					Minimum: Rational{Numerator: -100000, Denominator: 1},
					Maximum: Rational{Numerator: 100000, Denominator: 1},
					Unit:    "u", Presence: AlwaysPresent{},
				}},
			}},
		}
		if _, err := c.ParseDBC(ctx, sent); err != nil {
			t.Logf("ParseDBC refused %d bits at %d, factor %v: %v", length, start, factor, err)
			return false
		}
		got, err := c.FormatDBC(ctx)
		if err != nil {
			t.Logf("FormatDBC: %v", err)
			return false
		}
		if len(got.Messages) != 1 || len(got.Messages[0].Signals) != 1 {
			return false
		}
		back := got.Messages[0].Signals[0]
		return back.Name == "Sig" && back.StartBit == start && back.BitLength == length &&
			back.Factor.Numerator*factor.Denominator == factor.Numerator*back.Factor.Denominator &&
			back.Offset.Numerator*offset.Denominator == offset.Numerator*back.Offset.Denominator
	}
	if err := quick.Check(property, &quick.Config{MaxCount: 25}); err != nil {
		t.Errorf("a definition did not come back as it was sent: %v", err)
	}
}
