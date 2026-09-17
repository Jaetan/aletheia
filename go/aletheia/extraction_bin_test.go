// SPDX-FileCopyrightText: 2025 Nicolas Pelletier
// SPDX-License-Identifier: BSD-2-Clause

// Crafted byte vectors for parseExtractionBin, which decodes the packed
// binary extraction wire that the processExtractBin header comment in
// src/Aletheia/Main/Binary.agda documents. Nothing here calls the library:
// the decoder is pure. The vectors that decode show that a reason comes off
// the wire whole and that the offsets are byte counts; the vectors that are
// refused pin the exact total size, the three offsets invariants the wire
// doc tells decoders to verify, and UTF-8 on every reason.

package aletheia

import (
	"bytes"
	"encoding/binary"
	"errors"
	"log/slog"
	"strings"
	"testing"
	"unsafe"
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

// binExtractionErrors builds an errors-only buffer carrying the reasons,
// error i taking index i and code i. A nil offsets derives the cumulative
// table; a given one is written as it is, which is how a buffer that breaks
// an invariant is crafted. FuzzDecodeBinaryFrame seeds from it too.
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

// A buffer with one value, two errors and one absent signal decodes whole.
// The first reason carries a character two bytes wide, so the second slices
// correctly only if the offsets are read as byte counts; a character count
// would misalign every slice after it. The reasons arrive byte for byte,
// since they are the kernel's own strings and not a rendering of the code.
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

// A code outside the kernel's table (extractionErrorCodeToℕ in
// Aletheia.CAN.BatchExtraction) is carried, not refused: the code is there
// for a machine to read and the reason beside it is what the caller sees.
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

// With no errors the offsets table is still there, the single entry zero,
// and the buffer decodes to no errors.
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

// Every buffer the decoder cannot trust is refused with a protocol error
// naming the reason: a header shorter than its ten bytes, a total size that
// is off by a byte either way, an offsets table that starts past zero,
// decreases, or ends anywhere but at the reason bytes the header declares,
// and a reason slice that is not UTF-8, which every binding refuses.
func TestParseExtractionBin_RefusesMalformedBuffers(t *testing.T) {
	good := buildExtractionBin([]binVal{{idx: 0, num: 1, den: 2}}, nil, []uint32{0}, nil, nil)
	if _, err := parseExtractionBin(good, []string{"Sig"}); err != nil {
		t.Fatalf("the control buffer must decode: %v", err)
	}
	oneError := func(offsets []uint32, blob []byte) []byte {
		return buildExtractionBin(nil, []binErr{{idx: 0, code: 0}}, offsets, blob, nil)
	}
	cases := map[string]struct {
		buf    []byte
		names  []string
		substr string
	}{
		"empty":                {nil, nil, "too short"},
		"header cut short":     {make([]byte, 6), nil, "too short"},
		"header one byte shy":  {make([]byte, 9), nil, "too short"},
		"a byte too many":      {append(append([]byte{}, good...), 0x00), []string{"Sig"}, "size mismatch"},
		"a byte too few":       {good[:len(good)-1], []string{"Sig"}, "size mismatch"},
		"offsets start past 0": {oneError([]uint32{1, 4}, []byte("abcd")), []string{"Sig"}, "start at 0"},
		"offsets decrease": {buildExtractionBin(nil, []binErr{{idx: 0, code: 0}, {idx: 1, code: 0}},
			[]uint32{0, 3, 2}, []byte("ab"), nil), []string{"A", "B"}, "not monotone"},
		"offsets end elsewhere": {oneError([]uint32{0, 2}, []byte("boom")), []string{"Sig"}, "offsets end at"},
		"reason is not UTF-8":   {oneError([]uint32{0, 2}, []byte{0xFF, 0xFE}), []string{"Sig"}, "not valid UTF-8"},
	}
	for name, tc := range cases {
		t.Run(name, func(t *testing.T) {
			requireExtractionProtocolError(t, tc.buf, tc.names, tc.substr)
		})
	}
}

// corruptBinBackend answers the binary extraction with what the test sets:
// a buffer that does not parse, or an error other than the fallback sentinel.
type corruptBinBackend struct {
	routingBackend
	buf []byte
	err error
}

func (b *corruptBinBackend) ExtractSignalsBin(_ unsafe.Pointer, _ CANID, _ DLC, _ []byte) ([]byte, error) {
	return b.buf, b.err
}

// A binary extraction that returns a buffer that does not parse, or fails with
// anything but the fallback sentinel, yields no result and one warning naming
// the failure; the JSON path is not tried.
func TestExtractSignalsLocked_CorruptBinaryIsLoggedAndSkipped(t *testing.T) {
	cases := map[string]struct {
		buf   []byte
		err   error
		event string
	}{
		"a buffer that does not parse":     {[]byte{1}, nil, "extraction.parse_failed"},
		"an error other than the sentinel": {nil, errors.New("boom"), "extraction.process_failed"},
	}
	for name, tc := range cases {
		t.Run(name, func(t *testing.T) {
			var logged bytes.Buffer
			logger := slog.New(slog.NewTextHandler(&logged, &slog.HandlerOptions{Level: slog.LevelDebug}))
			b := &corruptBinBackend{buf: tc.buf, err: tc.err}
			b.hook = func(int) (string, error) { return `{"status":"success"}`, nil }
			c, err := NewClient(b, WithLogger(logger))
			if err != nil {
				t.Fatal(err)
			}
			t.Cleanup(func() { _ = c.Close() })
			sid, _ := NewStandardID(0x100)
			dlc, _ := NewDLC(8)
			c.signalNames = map[uint64][]string{canIDKey(sid): {"S"}}

			if got := c.extractSignalsLocked(ctx, sid, dlc, FramePayload{0, 0, 0, 0, 0, 0, 0, 0}); got != nil {
				t.Errorf("expected no result, got %+v", got)
			}
			if !strings.Contains(logged.String(), tc.event) {
				t.Errorf("expected %s in the log, got %q", tc.event, logged.String())
			}
			if b.callCount() != 0 {
				t.Errorf("the JSON path was tried %d times after a binary failure", b.callCount())
			}
		})
	}
}

// binExtractionValue builds a buffer holding one value and nothing else: the
// header, the value as its index and its numerator and denominator, and the
// single offsets entry zero.
func binExtractionValue(num, den int64) []byte {
	buf := make([]byte, 10+18+4)
	binary.LittleEndian.PutUint16(buf[0:2], 1) // one value
	// The error and absent counts, the reason bytes and the single offsets
	// entry are all zero already.
	binary.LittleEndian.PutUint16(buf[10:12], 0) // the value's signal index
	binary.LittleEndian.PutUint64(buf[12:20], uint64(num))
	binary.LittleEndian.PutUint64(buf[20:28], uint64(den))
	return buf
}

// A denominator of zero or less is a corrupt buffer, not a value: the binary
// path refuses it as the JSON path does, rather than building a rational the
// kernel renderer would be handed.
func TestParseExtractionBin_RejectsNonPositiveDenominator(t *testing.T) {
	for _, den := range []int64{0, -3} {
		if _, err := parseExtractionBin(binExtractionValue(1, den), []string{"Sig"}); err == nil {
			t.Errorf("den=%d: expected an error for a non-positive denominator, got nil", den)
		}
	}
	res, err := parseExtractionBin(binExtractionValue(1, 3), []string{"Sig"})
	if err != nil {
		t.Fatalf("den=3: unexpected error: %v", err)
	}
	if want := (Rational{Numerator: 1, Denominator: 3}); res.Values[0].Value != want {
		t.Errorf("got %v, want %v", res.Values[0].Value, want)
	}
}
