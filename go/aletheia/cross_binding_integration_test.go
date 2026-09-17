//go:build cgo && linux

// SPDX-FileCopyrightText: 2025 Nicolas Pelletier
// SPDX-License-Identifier: BSD-2-Clause

// The Go third of the cross-binding integration tests, with
// python/tests/test_cross_binding_integration.py and
// cpp/tests/test_cross_binding_integration.cpp. The three build identical
// canonical inputs in code and assert the structural invariants
// docs/architecture/PROTOCOL.md documents: field presence, value types,
// counts, error-code identity. A binding's drift from the protocol shows in
// its own suite and parity is transitive through the document; there is no
// shared corpus and no pairwise diff, since a corpus would tie every binding
// to one binding's emitted bytes.

package aletheia

import (
	"context"
	"errors"
	"strings"
	"testing"
)

// canonicalDBC is the fixture the Python and C++ tests define identically
// (_CANONICAL_DBC and canonical_dbc); drift between the three copies is one
// of the hazards these tests exist to catch.
func canonicalDBC() DBCDefinition {
	sid, d := canonicalFrameIDs()
	return DBCDefinition{
		Version: "1.0",
		Messages: []DBCMessage{
			{
				ID:     sid,
				Name:   "TestMessage",
				DLC:    d,
				Sender: "ECU",
				Signals: []DBCSignal{
					{
						Name:      "TestSignal",
						StartBit:  0,
						BitLength: 16,
						ByteOrder: LittleEndian,
						IsSigned:  false,
						Factor:    Rational{Numerator: 1, Denominator: 1},
						Offset:    Rational{Numerator: 0, Denominator: 1},
						Minimum:   Rational{Numerator: 0, Denominator: 1},
						Maximum:   Rational{Numerator: 65535, Denominator: 1},
						Unit:      "",
						Presence:  AlwaysPresent{},
					},
				},
			},
		},
	}
}

// canonicalFrameIDs is the canonical message's CAN ID and DLC.
func canonicalFrameIDs() (StandardID, DLC) {
	sid, _ := NewStandardID(256)
	d, _ := NewDLC(8)
	return sid, d
}

// streamingCrossBindingClient loads the canonical DBC, installs the given
// properties, starts the stream, and ends it when the test ends.
func streamingCrossBindingClient(t *testing.T, properties ...Formula) (*Client, context.Context) {
	t.Helper()
	c := newFFIClient(t)
	ctx := context.Background()
	if _, err := c.ParseDBC(ctx, canonicalDBC()); err != nil {
		t.Fatalf("ParseDBC: %v", err)
	}
	if len(properties) > 0 {
		if err := c.SetProperties(ctx, properties); err != nil {
			t.Fatalf("SetProperties: %v", err)
		}
	}
	if err := c.StartStream(ctx); err != nil {
		t.Fatalf("StartStream: %v", err)
	}
	t.Cleanup(func() {
		if _, err := c.EndStream(ctx); err != nil {
			t.Errorf("EndStream: %v", err)
		}
	})
	return c, ctx
}

// sendCanonical sends one frame on the canonical message.
func sendCanonical(t *testing.T, c *Client, ctx context.Context, ts int64, payload FramePayload, brs, esi *bool) FrameResponse {
	t.Helper()
	sid, d := canonicalFrameIDs()
	resp, err := c.SendFrame(ctx, Timestamp{Microseconds: ts}, sid, d, payload, brs, esi)
	if err != nil {
		t.Fatalf("SendFrame: %v", err)
	}
	return resp
}

// ParseDBC answers with ParsedDBC{DBC, Warnings}: Warnings is never nil, since
// Python emits [] and not None, and the message and signal names come back.
func TestCrossBinding_ParseDBCResponseShape(t *testing.T) {
	c := newFFIClient(t)
	parsed, err := c.ParseDBC(context.Background(), canonicalDBC())
	if err != nil {
		t.Fatalf("ParseDBC: %v", err)
	}
	if parsed == nil {
		t.Fatal("ParseDBC returned nil ParsedDBC")
	}
	if parsed.Warnings == nil {
		t.Error("ParsedDBC.Warnings: want non-nil (possibly empty), got nil")
	}
	if len(parsed.DBC.Messages) != 1 {
		t.Fatalf("ParsedDBC.DBC.Messages: want 1, got %d", len(parsed.DBC.Messages))
	}
	if got := parsed.DBC.Messages[0].Name; got != "TestMessage" {
		t.Errorf("Messages[0].Name: want TestMessage, got %q", got)
	}
	if len(parsed.DBC.Messages[0].Signals) != 1 {
		t.Fatalf("Messages[0].Signals: want 1, got %d", len(parsed.DBC.Messages[0].Signals))
	}
	if got := parsed.DBC.Messages[0].Signals[0].Name; got != "TestSignal" {
		t.Errorf("Signals[0].Name: want TestSignal, got %q", got)
	}
}

// ValidateDBC answers with ValidationResult{HasErrors, Issues}; the canonical
// DBC has no errors and Issues is never nil.
func TestCrossBinding_ValidateDBCResponseShape(t *testing.T) {
	c := newFFIClient(t)
	result, err := c.ValidateDBC(context.Background(), canonicalDBC())
	if err != nil {
		t.Fatalf("ValidateDBC: %v", err)
	}
	if result == nil {
		t.Fatal("ValidateDBC returned nil ValidationResult")
	}
	if result.HasErrors {
		t.Errorf("HasErrors: want false on canonical DBC, got true; issues=%v", result.Issues)
	}
	if result.Issues == nil {
		t.Error("Issues: want non-nil (possibly empty), got nil")
	}
}

// A frame that violates nothing answers Ack.
func TestCrossBinding_SendFrameAck(t *testing.T) {
	c, ctx := streamingCrossBindingClient(t,
		Always{Inner: Atomic{Predicate: LessThan{Signal: "TestSignal", Value: IntRational(1000)}}})
	resp := sendCanonical(t, c, ctx, 1000, FramePayload{0, 0, 0, 0, 0, 0, 0, 0}, nil, nil)
	if _, ok := resp.(Ack); !ok {
		t.Errorf("response: want Ack, got %T (%+v)", resp, resp)
	}
}

// A violating frame answers a PropertyBatch whose violation carries a
// timestamp.
func TestCrossBinding_SendFrameViolation(t *testing.T) {
	c, ctx := streamingCrossBindingClient(t,
		Always{Inner: Atomic{Predicate: LessThan{Signal: "TestSignal", Value: IntRational(100)}}})
	// 65535 > 100
	resp := sendCanonical(t, c, ctx, 1000, FramePayload{0xFF, 0xFF, 0, 0, 0, 0, 0, 0}, nil, nil)
	b, ok := resp.(PropertyBatch)
	if !ok {
		t.Fatalf("response: want PropertyBatch, got %T (%+v)", resp, resp)
	}
	v := b.FirstViolation()
	if v == nil {
		t.Fatalf("PropertyBatch.FirstViolation: want non-nil, batch=%+v", b)
	}
	if v.Timestamp == nil || v.Timestamp.Microseconds == 0 {
		t.Error("PropertyResult.Timestamp: want non-zero, got nil/0")
	}
}

// One frame can complete one property and violate another; the batch lists
// the satisfaction first and the violation last, in the kernel's
// dispatchIterResult order.
func TestCrossBinding_SendFrameMultiEvent(t *testing.T) {
	c, ctx := streamingCrossBindingClient(t,
		Eventually{Inner: Atomic{Predicate: Equals{Signal: "TestSignal", Value: IntRational(100)}}},
		Always{Inner: Atomic{Predicate: LessThan{Signal: "TestSignal", Value: IntRational(50)}}})
	// TestSignal = 100 completes the first property and violates the second
	resp := sendCanonical(t, c, ctx, 1000, FramePayload{100, 0, 0, 0, 0, 0, 0, 0}, nil, nil)
	b, ok := resp.(PropertyBatch)
	if !ok {
		t.Fatalf("response: want PropertyBatch, got %T (%+v)", resp, resp)
	}
	if len(b.Results) != 2 {
		t.Fatalf("PropertyBatch.Results: want 2 entries, got %d (%+v)", len(b.Results), b.Results)
	}
	if b.Results[0].Verdict != Holds || int(b.Results[0].PropertyIndex) != 0 {
		t.Errorf("Results[0]: want Holds for property 0, got %s for property %d", b.Results[0].Verdict, b.Results[0].PropertyIndex)
	}
	if b.Results[1].Verdict != Fails || int(b.Results[1].PropertyIndex) != 1 {
		t.Errorf("Results[1]: want Fails for property 1, got %s for property %d", b.Results[1].Verdict, b.Results[1].PropertyIndex)
	}
}

// An out-of-range CAN ID is refused by the type constructors before anything
// reaches the FFI, on the standard and the extended range; the Python and C++
// tests assert the same at their own type boundaries.
func TestCrossBinding_SendFrameError(t *testing.T) {
	if _, err := NewStandardID(0x800); err == nil {
		t.Error("NewStandardID(0x800): want error on out-of-range standard CAN ID, got nil")
	}
	if _, err := NewExtendedID(0x20000000); err == nil {
		t.Error("NewExtendedID(0x20000000): want error on out-of-range extended CAN ID, got nil")
	}
}

// The kernel carries the CAN-FD BRS and ESI bits without evaluating them:
// every combination of nil, true and false on an otherwise valid frame answers
// Ack (Python's test_canfd_brs_esi_passthrough is the same case).
func TestCrossBinding_SendFrameBrsEsiPassthrough(t *testing.T) {
	c, ctx := streamingCrossBindingClient(t)
	tval, fval := true, false
	options := []*bool{nil, &tval, &fval}
	var ts int64
	for _, brs := range options {
		for _, esi := range options {
			ts += 1000
			resp := sendCanonical(t, c, ctx, ts, FramePayload{0, 0, 0, 0, 0, 0, 0, 0}, brs, esi)
			if _, ok := resp.(Ack); !ok {
				t.Errorf("SendFrame brs=%v esi=%v: want Ack, got %T (%+v)", brs, esi, resp, resp)
			}
		}
	}
}

// identifierDBCText is a DBC text whose one message carries the given name.
func identifierDBCText(name string) string {
	return "VERSION \"\"\nNS_:\nBS_:\nBU_:\nBO_ 100 " + name + ": 8 ECU\n"
}

// An identifier of exactly MaxIdentifierLength parses and comes back whole.
func TestCrossBinding_IdentifierAtMaxLengthAccepted(t *testing.T) {
	c := newFFIClient(t)
	name := strings.Repeat("A", MaxIdentifierLength)
	parsed, err := c.ParseDBCText(context.Background(), identifierDBCText(name))
	if err != nil {
		t.Fatalf("expected success, got error: %v", err)
	}
	if got := string(parsed.DBC.Messages[0].Name); got != name {
		t.Errorf("Messages[0].Name length = %d, want %d", len(got), len(name))
	}
}

// An identifier one character past MaxIdentifierLength is refused by the
// kernel's identifier check and surfaces as a parse error whose code is the
// trailing-input one, because the parser stops where the identifier does.
func TestCrossBinding_IdentifierOverMaxRejected(t *testing.T) {
	c := newFFIClient(t)
	name := strings.Repeat("A", MaxIdentifierLength+1)
	_, err := c.ParseDBCText(context.Background(), identifierDBCText(name))
	if err == nil {
		t.Fatal("expected a parse error for an identifier one past the limit, got nil")
	}
	var aErr *Error
	if !errors.As(err, &aErr) {
		t.Fatalf("expected *aletheia.Error, got %T: %v", err, err)
	}
	if aErr.Code != CodeDBCTextTrailingInput {
		t.Errorf("Code = %q, want %q", aErr.Code, CodeDBCTextTrailingInput)
	}
}

// The shared entry gate refuses a signal whose start bit lies past the frame,
// on the JSON route, with a typed parse error naming the submitted value
// (Python's TestGeometryGateParity is the same case).
func TestCrossBinding_GeometryGateRefusesOutOfFrameStartBit(t *testing.T) {
	c := newFFIClient(t)
	sid, _ := NewStandardID(256)
	d, _ := NewDLC(1)
	dbc := DBCDefinition{
		Version: "1.0",
		Messages: []DBCMessage{{
			ID: sid, Name: "Tiny", DLC: d, Sender: "ECU",
			Signals: []DBCSignal{{
				Name:      "OutOfFrame",
				StartBit:  8, // the first bit past a 1-byte frame
				BitLength: 8,
				ByteOrder: LittleEndian,
				Factor:    Rational{Numerator: 1, Denominator: 1},
				Offset:    Rational{Numerator: 0, Denominator: 1},
				Minimum:   Rational{Numerator: 0, Denominator: 1},
				Maximum:   Rational{Numerator: 255, Denominator: 1},
				Presence:  AlwaysPresent{},
			}},
		}},
	}
	_, err := c.ParseDBC(context.Background(), dbc)
	if err == nil {
		t.Fatal("expected the entry gate to refuse an out-of-frame start bit")
	}
	var aErr *Error
	if !errors.As(err, &aErr) {
		t.Fatalf("expected *aletheia.Error, got %T: %v", err, err)
	}
	if aErr.Code != CodeParseSignalStartBitExceedsFrame {
		t.Errorf("Code = %q, want %q", aErr.Code, CodeParseSignalStartBitExceedsFrame)
	}
	if !strings.Contains(aErr.Message, "8") {
		t.Errorf("Message = %q, want it to name the submitted start bit", aErr.Message)
	}
}

// A full-frame Motorola signal (MSB at bit 7, descending through a DLC-2
// frame) loads on the text route, and the same document is accepted back on
// the JSON route with the same geometry.
func TestCrossBinding_MotorolaFullFrameClosure(t *testing.T) {
	c := newFFIClient(t)
	ctx := context.Background()
	text := "VERSION \"\"\n\nNS_ :\n\nBS_:\n\nBU_: Engine\n\n" +
		"BO_ 100 Msg: 2 Engine\n" +
		" SG_ Sig : 7|16@0+ (1,0) [0|0] \"\" Engine\n"
	loaded, err := c.ParseDBCText(ctx, text)
	if err != nil {
		t.Fatalf("ParseDBCText: %v", err)
	}
	sig := loaded.DBC.Messages[0].Signals[0]
	if sig.StartBit != 7 || sig.BitLength != 16 {
		t.Fatalf("text route: got bits[%d:%d], want bits[7:16]",
			uint16(sig.StartBit), uint16(sig.BitLength))
	}
	echoed, err := c.ParseDBC(ctx, loaded.DBC)
	if err != nil {
		t.Fatalf("JSON route must accept the text-loaded document: %v", err)
	}
	sig = echoed.DBC.Messages[0].Signals[0]
	if sig.StartBit != 7 || sig.BitLength != 16 {
		t.Errorf("JSON route: got bits[%d:%d], want bits[7:16]",
			uint16(sig.StartBit), uint16(sig.BitLength))
	}
}

// A formula nested past MaxNestingDepth is refused by the kernel's depth
// check with an InputBoundExceeded error carrying bound kind, observed depth
// and limit, lifted to *InputBoundExceededError (Python's
// TestNestingDepthBound is the same case). The same lifter serves the
// AtomCount and IdentifierLength kinds; the AtomCount bound is exercised at
// the kernel and Python boundary (python/tests/test_input_bounds.py,
// TestAtomCountBound), a tree of that many atoms being too slow to build
// across the Go FFI for a unit test.
func TestCrossBinding_NestingDepthLiftsToInputBoundExceeded(t *testing.T) {
	c := newFFIClient(t)
	ctx := context.Background()
	if _, err := c.ParseDBC(ctx, canonicalDBC()); err != nil {
		t.Fatalf("ParseDBC: %v", err)
	}
	// the atomic and its predicate are two levels; MaxNestingDepth-1 wrappers
	// put the formula one level past the limit
	inner := Formula(Atomic{Predicate: Equals{Signal: "TestSignal", Value: IntRational(0)}})
	for range MaxNestingDepth - 1 {
		inner = Always{Inner: inner}
	}
	err := c.SetProperties(ctx, []Formula{inner})
	if err == nil {
		t.Fatal("expected InputBoundExceededError for a formula one past the depth limit, got nil")
	}
	var bex *InputBoundExceededError
	if !errors.As(err, &bex) {
		t.Fatalf("expected *InputBoundExceededError, got %T: %v", err, err)
	}
	if bex.Code != CodeInputBoundExceeded {
		t.Errorf("Code = %q, want %q", bex.Code, CodeInputBoundExceeded)
	}
	if bex.BoundKind != BoundKindNestingDepth {
		t.Errorf("BoundKind = %q, want %q", bex.BoundKind, BoundKindNestingDepth)
	}
	if bex.Limit != uint64(MaxNestingDepth) {
		t.Errorf("Limit = %d, want %d", bex.Limit, MaxNestingDepth)
	}
	if bex.Observed <= uint64(MaxNestingDepth) {
		t.Errorf("Observed = %d, want > %d", bex.Observed, MaxNestingDepth)
	}
}

// The error reason on the packed binary extraction wire is the kernel's
// detailed string, byte-identical to the JSON path's for the same frame: one
// shared kernel formatter, checked here end to end on an out-of-bounds value.
func TestCrossBinding_BinaryExtractionReasonParity(t *testing.T) {
	c := newFFIClient(t)
	ctx := context.Background()
	sid, d := canonicalFrameIDs()
	dbc := DBCDefinition{
		Version: "1.0",
		Messages: []DBCMessage{{
			ID:     sid,
			Name:   "TestMessage",
			DLC:    d,
			Sender: "ECU",
			Signals: []DBCSignal{{
				Name:      "BoundedSignal",
				StartBit:  0,
				BitLength: 16,
				ByteOrder: LittleEndian,
				IsSigned:  false,
				Factor:    Rational{Numerator: 1, Denominator: 4},
				Offset:    Rational{Numerator: 0, Denominator: 1},
				Minimum:   Rational{Numerator: 0, Denominator: 1},
				Maximum:   Rational{Numerator: 8000, Denominator: 1},
				Presence:  AlwaysPresent{},
			}},
		}},
	}
	if _, err := c.ParseDBC(ctx, dbc); err != nil {
		t.Fatalf("ParseDBC: %v", err)
	}
	// raw 65535 scales to 16383.75, above the 8000 maximum: one extraction error
	payload := FramePayload{0xFF, 0xFF, 0, 0, 0, 0, 0, 0}

	// the public ExtractSignals commits to the binary wire once the DBC is loaded
	binRes, err := c.ExtractSignals(ctx, sid, d, payload)
	if err != nil {
		t.Fatalf("ExtractSignals (binary path): %v", err)
	}
	if len(binRes.Errors) != 1 {
		t.Fatalf("binary path: len(Errors) = %d, want 1 (out-of-bounds)", len(binRes.Errors))
	}
	// the same frame through the backend's JSON extraction
	resp, err := c.backend.ExtractSignalsBinary(c.state, sid, d, []byte(payload))
	if err != nil {
		t.Fatalf("ExtractSignalsBinary (JSON path): %v", err)
	}
	jsonRes, err := parseExtractionResponse(resp)
	if err != nil {
		t.Fatalf("parseExtractionResponse: %v", err)
	}
	if len(jsonRes.Errors) != 1 {
		t.Fatalf("JSON path: len(Errors) = %d, want 1 (out-of-bounds)", len(jsonRes.Errors))
	}
	if binRes.Errors[0].Name != jsonRes.Errors[0].Name {
		t.Errorf("error name: binary %q != JSON %q", binRes.Errors[0].Name, jsonRes.Errors[0].Name)
	}
	if binRes.Errors[0].Error != jsonRes.Errors[0].Error {
		t.Errorf("error reason: binary %q != JSON %q", binRes.Errors[0].Error, jsonRes.Errors[0].Error)
	}
	if !strings.Contains(binRes.Errors[0].Error, "out of bounds") {
		t.Errorf("reason should be the detailed out-of-bounds string, got %q", binRes.Errors[0].Error)
	}
}
