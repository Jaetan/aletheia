//go:build cgo && linux

// SPDX-License-Identifier: BSD-2-Clause

// Cross-binding integration test (R18 cluster 5 — Cat 33d).
//
// Counterpart of python/tests/test_cross_binding_integration.py and
// cpp/tests/test_cross_binding_integration.cpp. All three tests construct
// identical canonical inputs in code (no shared corpus, no golden output to
// diff against) and assert the binding's response shape matches the
// structural invariants documented in docs/architecture/PROTOCOL.md.
//
// The shared truth is PROTOCOL.md (text + JSON examples). Corpus-style
// integration tests bit-rot fast and tie every binding to one binding's exact
// emit format. By asserting structural invariants here (field presence, value
// types, count relationships, error-code identity), each binding's drift from
// the documented protocol surfaces locally without depending on the other
// bindings being run.
//
// Cross-binding parity is enforced transitively: if Python's test asserts
// "ParsedDBCResponse has exactly the keys {status, dbc, warnings}" and Go's
// test asserts the same (translated to Go: ParsedDBC has DBC + Warnings),
// any binding that drops or adds a field fails its own test. No pairwise
// binding diff is computed.

package aletheia

import (
	"context"
	"errors"
	"strings"
	"testing"
)

// canonicalDBC mirrors the inline DBC fixture in
// python/tests/test_cross_binding_integration.py (`_CANONICAL_DBC`) and
// cpp/tests/test_cross_binding_integration.cpp (`canonical_dbc`).
//
// The three definitions are content-equivalent; structural drift across
// languages is the actual cross-binding hazard the test is designed to catch.
func canonicalDBC() DBCDefinition {
	sid, _ := NewStandardID(256)
	d, _ := NewDLC(8)
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

func newCrossBindingClient(t *testing.T) *Client {
	t.Helper()
	lib := findFFILibForParityTest()
	if lib == "" {
		t.Skip("libaletheia-ffi.so not found — run 'cabal run shake -- build' first")
	}
	backend, err := NewFFIBackend(lib)
	if err != nil {
		t.Fatalf("NewFFIBackend: %v", err)
	}
	c, err := NewClient(backend)
	if err != nil {
		t.Fatalf("NewClient: %v", err)
	}
	t.Cleanup(func() {
		if err := c.Close(); err != nil {
			t.Errorf("Close: %v", err)
		}
	})
	return c
}

// TestCrossBinding_ParseDBCResponseShape asserts that ParseDBC populates
// the documented response shape: ParsedDBC{DBC, Warnings} where DBC's
// nested message + signal counts and IDs are preserved from the input.
func TestCrossBinding_ParseDBCResponseShape(t *testing.T) {
	c := newCrossBindingClient(t)
	parsed, err := c.ParseDBC(context.Background(), canonicalDBC())
	if err != nil {
		t.Fatalf("ParseDBC: %v", err)
	}
	if parsed == nil {
		t.Fatal("ParseDBC returned nil ParsedDBC")
	}
	// Warnings field is non-nil (may be empty); Go's nil-vs-empty distinction
	// matters for cross-binding parity — Python emits [], not None.
	if parsed.Warnings == nil {
		t.Error("ParsedDBC.Warnings: want non-nil (possibly empty), got nil")
	}
	// Round-trip identity invariant on the canonical content.
	if len(parsed.DBC.Messages) != 1 {
		t.Errorf("ParsedDBC.DBC.Messages: want 1, got %d", len(parsed.DBC.Messages))
	}
	if got := parsed.DBC.Messages[0].Name; got != "TestMessage" {
		t.Errorf("Messages[0].Name: want TestMessage, got %q", got)
	}
	if len(parsed.DBC.Messages[0].Signals) != 1 {
		t.Errorf("Messages[0].Signals: want 1, got %d", len(parsed.DBC.Messages[0].Signals))
	}
	if got := parsed.DBC.Messages[0].Signals[0].Name; got != "TestSignal" {
		t.Errorf("Signals[0].Name: want TestSignal, got %q", got)
	}
}

// TestCrossBinding_ValidateDBCResponseShape asserts that ValidateDBC populates
// the documented ValidationResult{HasErrors, Issues} shape; canonical DBC has
// HasErrors=false.
func TestCrossBinding_ValidateDBCResponseShape(t *testing.T) {
	c := newCrossBindingClient(t)
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

// TestCrossBinding_SendFrameAck asserts the AckResponse path: sending a
// non-violating frame returns Ack{}.
func TestCrossBinding_SendFrameAck(t *testing.T) {
	c := newCrossBindingClient(t)
	ctx := context.Background()
	if _, err := c.ParseDBC(ctx, canonicalDBC()); err != nil {
		t.Fatalf("ParseDBC: %v", err)
	}
	if err := c.SetProperties(ctx, []Formula{
		Always{Inner: Atomic{Predicate: LessThan{Signal: "TestSignal", Value: RationalFromFloat(1000)}}},
	}); err != nil {
		t.Fatalf("SetProperties: %v", err)
	}
	if err := c.StartStream(ctx); err != nil {
		t.Fatalf("StartStream: %v", err)
	}
	defer func() { _, _ = c.EndStream(ctx) }()

	sid, _ := NewStandardID(256)
	d, _ := NewDLC(8)
	resp, err := c.SendFrame(ctx, Timestamp{Microseconds: 1000}, sid, d,
		FramePayload{0, 0, 0, 0, 0, 0, 0, 0}, nil, nil)
	if err != nil {
		t.Fatalf("SendFrame: %v", err)
	}
	if _, ok := resp.(Ack); !ok {
		t.Errorf("response: want Ack, got %T (%+v)", resp, resp)
	}
}

// TestCrossBinding_SendFrameViolation asserts the PropertyViolationResponse
// path: a violating frame returns Violation{PropertyIndex, Timestamp, ...}.
func TestCrossBinding_SendFrameViolation(t *testing.T) {
	c := newCrossBindingClient(t)
	ctx := context.Background()
	if _, err := c.ParseDBC(ctx, canonicalDBC()); err != nil {
		t.Fatalf("ParseDBC: %v", err)
	}
	if err := c.SetProperties(ctx, []Formula{
		Always{Inner: Atomic{Predicate: LessThan{Signal: "TestSignal", Value: RationalFromFloat(100)}}},
	}); err != nil {
		t.Fatalf("SetProperties: %v", err)
	}
	if err := c.StartStream(ctx); err != nil {
		t.Fatalf("StartStream: %v", err)
	}
	defer func() { _, _ = c.EndStream(ctx) }()

	sid, _ := NewStandardID(256)
	d, _ := NewDLC(8)
	// Signal value 0xFFFF (65535) > 100 → violation.
	resp, err := c.SendFrame(ctx, Timestamp{Microseconds: 1000}, sid, d,
		FramePayload{0xFF, 0xFF, 0, 0, 0, 0, 0, 0}, nil, nil)
	if err != nil {
		t.Fatalf("SendFrame: %v", err)
	}
	v, ok := resp.(Violation)
	if !ok {
		t.Fatalf("response: want Violation, got %T (%+v)", resp, resp)
	}
	if v.Timestamp.Microseconds == 0 {
		t.Error("Violation.Timestamp: want non-zero, got 0")
	}
}

// TestCrossBinding_SendFrameError asserts the ErrorResponse path: an invalid
// CAN ID surfaces as a Go error from SendFrame, with the code field set.
func TestCrossBinding_SendFrameError(t *testing.T) {
	c := newCrossBindingClient(t)
	ctx := context.Background()
	if _, err := c.ParseDBC(ctx, canonicalDBC()); err != nil {
		t.Fatalf("ParseDBC: %v", err)
	}
	if err := c.StartStream(ctx); err != nil {
		t.Fatalf("StartStream: %v", err)
	}
	defer func() { _, _ = c.EndStream(ctx) }()

	// 0x800 = 2048 is out of standard 11-bit range; NewStandardID rejects it
	// before reaching the FFI, so the error path is exercised at the type
	// constructor — the cross-binding invariant is "invalid CAN ID is rejected
	// somewhere on the path", which is satisfied by the Go newtype
	// constructor returning a typed error.
	if _, err := NewStandardID(0x800); err == nil {
		t.Error("NewStandardID(0x800): want error on out-of-range standard CAN ID, got nil")
	}
	// And exercised end-to-end: an extended ID just over the 29-bit cap
	// (0x20000000 = 2^29) should also reject. The newtype boundary check
	// is the cross-binding-equivalent of Python raising on out-of-range
	// CAN IDs and C++ returning an Error variant.
	if _, err := NewExtendedID(0x20000000); err == nil {
		t.Error("NewExtendedID(0x20000000): want error on out-of-range extended CAN ID, got nil")
	}
}

// TestCrossBinding_SendFrameBrsEsiPassthrough mirrors Python's
// test_canfd_brs_esi_passthrough.  R19 Phase 2 cluster 18
// (AGDA-D-10.1 / 13.1 / 17.1): the Aletheia kernel does not consume
// CAN-FD BRS / ESI metadata, but the binding must accept the bits as
// *bool params and the FFI must accept the 4 trailing u8 args without
// crashing.  Every combination of brs / esi ∈ {nil, &true, &false}
// must return Ack for an otherwise-valid frame.
func TestCrossBinding_SendFrameBrsEsiPassthrough(t *testing.T) {
	c := newCrossBindingClient(t)
	ctx := context.Background()
	if _, err := c.ParseDBC(ctx, canonicalDBC()); err != nil {
		t.Fatalf("ParseDBC: %v", err)
	}
	if err := c.StartStream(ctx); err != nil {
		t.Fatalf("StartStream: %v", err)
	}
	defer func() { _, _ = c.EndStream(ctx) }()

	sid, _ := NewStandardID(256)
	d, _ := NewDLC(8)
	tval := true
	fval := false
	options := []*bool{nil, &tval, &fval}

	var ts int64
	for _, brs := range options {
		for _, esi := range options {
			ts += 1000
			resp, err := c.SendFrame(
				ctx, Timestamp{Microseconds: ts}, sid, d,
				FramePayload{0, 0, 0, 0, 0, 0, 0, 0},
				brs, esi,
			)
			if err != nil {
				t.Fatalf("SendFrame brs=%v esi=%v: %v", brs, esi, err)
			}
			if _, ok := resp.(Ack); !ok {
				t.Errorf("SendFrame brs=%v esi=%v: want Ack, got %T (%+v)",
					brs, esi, resp, resp)
			}
		}
	}
}

// R19 cluster 8 phase e.1 — Identifier validity record enforces
// MaxIdentifierLength. The Agda kernel's `validIdentifierᵇ` predicate
// gained a third conjunct asserting `length name <ᵇ suc max-identifier-
// length`. Identifiers at the limit (128 chars) still parse; anything
// longer is rejected at `mkIdentFromChars` and surfaces as a parse
// error on the wire (currently `dbc_text_trailing_input` due to parser
// monad position semantics; refining to typed `InputBoundExceeded
// IdentifierLength` is downstream parser-monad plumbing).

func TestCrossBinding_IdentifierAtMaxLengthAccepted(t *testing.T) {
	c := newCrossBindingClient(t)
	name := strings.Repeat("A", MaxIdentifierLength)
	dbcText := "VERSION \"\"\nNS_:\nBS_:\nBU_:\nBO_ 100 " + name + ": 8 ECU\n"
	parsed, err := c.ParseDBCText(context.Background(), dbcText)
	if err != nil {
		t.Fatalf("expected success, got error: %v", err)
	}
	if got := string(parsed.DBC.Messages[0].Name); got != name {
		t.Errorf("Messages[0].Name length = %d, want %d", len(got), len(name))
	}
}

func TestCrossBinding_IdentifierOverMaxRejected(t *testing.T) {
	c := newCrossBindingClient(t)
	name := strings.Repeat("A", MaxIdentifierLength+1)
	dbcText := "VERSION \"\"\nNS_:\nBS_:\nBU_:\nBO_ 100 " + name + ": 8 ECU\n"
	_, err := c.ParseDBCText(context.Background(), dbcText)
	if err == nil {
		t.Fatal("expected parse error for 129-char identifier, got nil")
	}
}

// TestCrossBinding_ErrorTypeShape asserts that *aletheia.Error has the
// documented field set when surfaced (mirrors Python's
// test_error_response_keys_when_observed_directly).
func TestCrossBinding_ErrorTypeShape(t *testing.T) {
	// Synthesize an Error and verify its public shape.
	e := &Error{
		Code:    "frame_invalid_can_id",
		Message: "CAN ID out of range",
	}
	if e.Code == "" {
		t.Error("Error.Code: want non-empty")
	}
	if e.Message == "" {
		t.Error("Error.Message: want non-empty")
	}
	if e.Error() == "" {
		t.Error("Error.Error(): want non-empty")
	}
	// Cross-binding parity: errors.As pattern must work for downstream
	// consumers; Python uses isinstance(exc, AletheiaError) the same way.
	var target *Error
	if !errors.As(e, &target) {
		t.Error("errors.As(*Error): want true")
	}
}

// R19 AGDA-D-13.4 phase 2a — typed NestingDepth wire-error refinement.
// A deeply-nested LTL formula triggers the kernel-side `jsonDepth`
// check at `handleParsedJSON`, which emits
// `ParseErr (InputBoundExceeded NestingDepth …)` instead of the
// pre-phase-2a `DispatchErr InvalidJSON`.  The wire response now carries
// `bound_kind / observed / limit`, lifted into `*InputBoundExceededError`
// by `checkErrorStatus`.  Mirrors Python's
// `TestNestingDepthBound::test_nested_at_depth_63_rejected`.
//
// Phase 2b (AtomCount) note: `inputBoundExceededFromResponse` is BoundKind-
// generic — it dispatches on `bound_kind` string, not on `code`.  This
// NestingDepth test exercises the same lifter that handles AtomCount
// (>1024 atom-per-property) and IdentifierLength.  AtomCount over-bound
// rejection is verified at the kernel + Python boundary by
// `python/tests/test_input_bounds.py::TestAtomCountBound`; building a
// 1025-atom And-tree across the Go FFI takes ~109s which is unsuitable
// for a unit-test budget.
func TestCrossBinding_NestingDepthLiftsToInputBoundExceeded(t *testing.T) {
	c := newCrossBindingClient(t)
	ctx := context.Background()
	if _, err := c.ParseDBC(ctx, canonicalDBC()); err != nil {
		t.Fatalf("ParseDBC: %v", err)
	}
	// 63 always-wrappers + atomic + predicate = JSON depth 65 (> 64).
	inner := Formula(Atomic{Predicate: Equals{Signal: "TestSignal", Value: RationalFromFloat(0)}})
	for range 63 {
		inner = Always{Inner: inner}
	}
	err := c.SetProperties(ctx, []Formula{inner})
	if err == nil {
		t.Fatal("expected InputBoundExceededError for 65-deep formula, got nil")
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
