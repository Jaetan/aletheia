// SPDX-FileCopyrightText: 2025 Nicolas Pelletier
// SPDX-License-Identifier: BSD-2-Clause

// Crafted-byte-vector tests for parseExtractionBin, the decoder of the packed
// binary extraction wire (canonical wire doc: the processExtractBin header
// comment in src/Aletheia/Main/Binary.agda). Pure decoder tests — no FFI/RTS.
// Each reject vector pins one of the decoder's protocol invariants: the exact
// total-size check, the three offsets-table invariants, and per-reason UTF-8
// validation. The happy-path vector proves reasons are surfaced from the wire
// and that offsets are byte counts, not character counts.

package aletheia

import (
	"encoding/binary"
	"errors"
	"strings"
	"testing"
)

// binVal is one Values-segment entry: (idx:u16, num:i64, den:i64).
type binVal struct {
	idx      uint16
	num, den int64
}

// binErr is one Errors-segment entry: (idx:u16, code:u8).
type binErr struct {
	idx  uint16
	code uint8
}

// buildExtractionBin assembles a binary extraction wire buffer from raw
// segments. The header counts come from the slice lengths and reasonBytes
// from len(blob); offsets are written verbatim, so invariant-violating
// buffers (bad first offset, non-monotone, end mismatch) can be crafted.
func buildExtractionBin(vals []binVal, errs []binErr, offsets []uint32, blob []byte, absent []uint16) []byte {
	buf := make([]byte, 10+18*len(vals)+3*len(errs)+4*len(offsets)+len(blob)+2*len(absent))
	binary.LittleEndian.PutUint16(buf[0:2], uint16(len(vals)))
	binary.LittleEndian.PutUint16(buf[2:4], uint16(len(errs)))
	binary.LittleEndian.PutUint16(buf[4:6], uint16(len(absent)))
	binary.LittleEndian.PutUint32(buf[6:10], uint32(len(blob)))
	off := 10
	for _, v := range vals {
		binary.LittleEndian.PutUint16(buf[off:off+2], v.idx)
		binary.LittleEndian.PutUint64(buf[off+2:off+10], uint64(v.num))
		binary.LittleEndian.PutUint64(buf[off+10:off+18], uint64(v.den))
		off += 18
	}
	for _, e := range errs {
		binary.LittleEndian.PutUint16(buf[off:off+2], e.idx)
		buf[off+2] = e.code
		off += 3
	}
	for _, o := range offsets {
		binary.LittleEndian.PutUint32(buf[off:off+4], o)
		off += 4
	}
	off += copy(buf[off:], blob)
	for _, a := range absent {
		binary.LittleEndian.PutUint16(buf[off:off+2], a)
		off += 2
	}
	return buf
}

// binExtractionErrors builds an errors-only buffer carrying the given wire
// reasons (error i gets idx i and code i). offsets == nil derives the correct
// cumulative offsets table; a non-nil offsets is written verbatim to craft
// invariant-violating buffers. Also seeds FuzzDecodeBinaryFrame.
func binExtractionErrors(reasons []string, offsets []uint32) []byte {
	errs := make([]binErr, len(reasons))
	var blob []byte
	derived := make([]uint32, 0, len(reasons)+1)
	derived = append(derived, 0)
	for i, r := range reasons {
		errs[i] = binErr{idx: uint16(i), code: uint8(i)}
		blob = append(blob, r...)
		derived = append(derived, uint32(len(blob)))
	}
	if offsets == nil {
		offsets = derived
	}
	return buildExtractionBin(nil, errs, offsets, blob, nil)
}

// requireExtractionProtocolError asserts parseExtractionBin rejects buf with
// an ErrProtocol *Error whose message contains substr.
func requireExtractionProtocolError(t *testing.T, buf []byte, names []string, substr string) {
	t.Helper()
	_, err := parseExtractionBin(buf, names)
	if err == nil {
		t.Fatalf("expected protocol error containing %q, got nil", substr)
	}
	var aErr *Error
	if !errors.As(err, &aErr) || aErr.Kind != ErrProtocol {
		t.Fatalf("expected an ErrProtocol *Error, got %T: %v", err, err)
	}
	if !strings.Contains(err.Error(), substr) {
		t.Errorf("expected error containing %q, got %q", substr, err.Error())
	}
}

// TestParseExtractionBin_HappyPathWireReasons decodes a buffer with one
// value, two errors with distinct wire reasons, and one absent signal. The
// FIRST reason contains a multi-byte UTF-8 character, so the second reason
// slices correctly only if the offsets table is interpreted as byte counts
// (a character-count reading would misalign every following slice). The
// reasons must surface byte-identically — they are the kernel-minted detailed
// strings, not any binding-local rendering of the u8 code.
func TestParseExtractionBin_HappyPathWireReasons(t *testing.T) {
	names := []string{"Speed", "RPM", "Temp", "Mode"}
	r1 := "signal 'Tempé' not found in message"            // é is 2 bytes in UTF-8
	r2 := "value out of bounds: 16383.75 not in [0, 8000]" // distinct from r1
	buf := buildExtractionBin(
		[]binVal{{idx: 0, num: 5, den: 2}},
		[]binErr{{idx: 1, code: 0}, {idx: 2, code: 1}},
		[]uint32{0, uint32(len(r1)), uint32(len(r1) + len(r2))},
		[]byte(r1+r2),
		[]uint16{3},
	)
	res, err := parseExtractionBin(buf, names)
	if err != nil {
		t.Fatalf("parseExtractionBin: %v", err)
	}
	if len(res.Values) != 1 || res.Values[0].Name != "Speed" ||
		res.Values[0].Value != (Rational{Numerator: 5, Denominator: 2}) {
		t.Errorf("Values = %+v, want [{Speed 5/2}]", res.Values)
	}
	if len(res.Errors) != 2 {
		t.Fatalf("len(Errors) = %d, want 2", len(res.Errors))
	}
	if res.Errors[0].Name != "RPM" || res.Errors[0].Error != r1 {
		t.Errorf("Errors[0] = %+v, want {RPM %q}", res.Errors[0], r1)
	}
	if res.Errors[1].Name != "Temp" || res.Errors[1].Error != r2 {
		t.Errorf("Errors[1] = %+v, want {Temp %q}", res.Errors[1], r2)
	}
	if len(res.Absent) != 1 || res.Absent[0] != "Mode" {
		t.Errorf("Absent = %v, want [Mode]", res.Absent)
	}
}

// TestParseExtractionBin_UnknownCodeTransported pins the "unknown codes are
// not rejected" contract: the u8 code is transported for machine consumption
// and the wire reason is authoritative, so a code outside the table pinned by
// the Agda SSOT (extractionErrorCodeToℕ in Aletheia.CAN.BatchExtraction) must
// decode to the wire reason, not a protocol error.
func TestParseExtractionBin_UnknownCodeTransported(t *testing.T) {
	reason := "some future error class"
	buf := buildExtractionBin(nil,
		[]binErr{{idx: 0, code: 0xFF}},
		[]uint32{0, uint32(len(reason))},
		[]byte(reason),
		nil,
	)
	res, err := parseExtractionBin(buf, []string{"Sig"})
	if err != nil {
		t.Fatalf("unknown code must not be rejected: %v", err)
	}
	if len(res.Errors) != 1 || res.Errors[0].Error != reason {
		t.Errorf("Errors = %+v, want the wire reason %q", res.Errors, reason)
	}
}

// TestParseExtractionBin_ZeroErrorsSingleOffsetEntry pins the nErrors == 0
// shape: the offsets table is still present as the single entry 0 with
// reasonBytes 0, and the buffer decodes to an empty errors partition.
func TestParseExtractionBin_ZeroErrorsSingleOffsetEntry(t *testing.T) {
	buf := buildExtractionBin([]binVal{{idx: 0, num: 7, den: 1}}, nil, []uint32{0}, nil, nil)
	res, err := parseExtractionBin(buf, []string{"Sig"})
	if err != nil {
		t.Fatalf("parseExtractionBin: %v", err)
	}
	if len(res.Errors) != 0 {
		t.Errorf("Errors = %+v, want empty", res.Errors)
	}
	if len(res.Values) != 1 || res.Values[0].Value != (Rational{Numerator: 7, Denominator: 1}) {
		t.Errorf("Values = %+v, want [{Sig 7/1}]", res.Values)
	}
}

// TestParseExtractionBin_TruncatedHeader rejects buffers shorter than the
// 10-byte header.
func TestParseExtractionBin_TruncatedHeader(t *testing.T) {
	for _, n := range []int{0, 6, 9} {
		requireExtractionProtocolError(t, make([]byte, n), nil, "too short")
	}
}

// TestParseExtractionBin_TotalSizeMismatch pins the exact total-size check:
// both a trailing extra byte and a missing byte are protocol errors.
func TestParseExtractionBin_TotalSizeMismatch(t *testing.T) {
	good := buildExtractionBin([]binVal{{idx: 0, num: 1, den: 2}}, nil, []uint32{0}, nil, nil)
	if _, err := parseExtractionBin(good, []string{"Sig"}); err != nil {
		t.Fatalf("control buffer must decode: %v", err)
	}
	requireExtractionProtocolError(t, append(append([]byte{}, good...), 0x00), []string{"Sig"}, "size mismatch")
	requireExtractionProtocolError(t, good[:len(good)-1], []string{"Sig"}, "size mismatch")
}

// TestParseExtractionBin_OffsetsFirstNonZero rejects an offsets table whose
// first entry is not 0.
func TestParseExtractionBin_OffsetsFirstNonZero(t *testing.T) {
	buf := buildExtractionBin(nil, []binErr{{idx: 0, code: 0}}, []uint32{1, 4}, []byte("abcd"), nil)
	requireExtractionProtocolError(t, buf, []string{"Sig"}, "start at 0")
}

// TestParseExtractionBin_OffsetsNonMonotone rejects a decreasing offsets
// table. The end entry equals reasonBytes so only the monotonicity invariant
// is violated.
func TestParseExtractionBin_OffsetsNonMonotone(t *testing.T) {
	buf := buildExtractionBin(nil, []binErr{{idx: 0, code: 0}, {idx: 1, code: 0}}, []uint32{0, 3, 2}, []byte("ab"), nil)
	requireExtractionProtocolError(t, buf, []string{"A", "B"}, "not monotone")
}

// TestParseExtractionBin_OffsetsEndMismatch rejects an offsets table whose
// last entry differs from the header's reasonBytes.
func TestParseExtractionBin_OffsetsEndMismatch(t *testing.T) {
	buf := buildExtractionBin(nil, []binErr{{idx: 0, code: 0}}, []uint32{0, 2}, []byte("boom"), nil)
	requireExtractionProtocolError(t, buf, []string{"Sig"}, "offsets end at")
}

// TestParseExtractionBin_InvalidUTF8Reason rejects a reason slice that is not
// valid UTF-8 — all four bindings reject invalid reason bytes symmetrically.
func TestParseExtractionBin_InvalidUTF8Reason(t *testing.T) {
	buf := buildExtractionBin(nil, []binErr{{idx: 0, code: 0}}, []uint32{0, 2}, []byte{0xFF, 0xFE}, nil)
	requireExtractionProtocolError(t, buf, []string{"Sig"}, "not valid UTF-8")
}
