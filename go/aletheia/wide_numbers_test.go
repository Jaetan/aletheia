//go:build cgo && linux

// SPDX-FileCopyrightText: 2025 Nicolas Pelletier
// SPDX-License-Identifier: BSD-2-Clause

// The numbers the kernel carries past 64 bits, through the real library.
// Each number kind has its own bound, decided by the kernel when it reads the
// number: a rational's numerator magnitude and denominator at most 2^128-1, a
// multiplex value at most 2^128-1, a value-description key signed with its
// magnitude at most 2^128-1, and a time bound at most 2^64-1 microseconds. A
// refusal past a bound whose measured value passes the reported ceiling names
// no number.

package aletheia

import (
	"bytes"
	"encoding/binary"
	"errors"
	"fmt"
	"math"
	"math/big"
	"reflect"
	"slices"
	"testing"
)

// u64Max is 2^64-1 as a rational.
var u64Max = Rational{Numerator: Uint128{Lo: math.MaxUint64}, Denominator: Uint128{Lo: 1}}

// vwMLBFactor is the factor opendbc's vw_mlb.dbc gives OBD_Abs_Load_Val:
// 100/255 printed to 17 places, so a value's reduced numerator passes 64 bits
// on most raw values.
var vwMLBFactor = big.NewRat(39215686274509803, 100_000_000_000_000_000)

// twoTo is 2^n.
func twoTo(n uint) *big.Int { return new(big.Int).Lsh(big.NewInt(1), n) }

// wideOf is x as a Uint128, failing the test for an x the type does not hold.
func wideOf(t *testing.T, x *big.Int) Uint128 {
	t.Helper()
	if x.Sign() < 0 || x.BitLen() > 128 {
		t.Fatalf("%s is not a 128-bit magnitude", x)
	}
	low := new(big.Int).And(x, new(big.Int).SetUint64(math.MaxUint64))
	return Uint128{Hi: new(big.Int).Rsh(x, 64).Uint64(), Lo: low.Uint64()}
}

// rationalOfRat is r as the Rational the kernel writes, reduced.
func rationalOfRat(t *testing.T, r *big.Rat) Rational {
	t.Helper()
	return Rational{
		Negative:    r.Sign() < 0,
		Numerator:   wideOf(t, new(big.Int).Abs(r.Num())),
		Denominator: wideOf(t, r.Denom()),
	}
}

// unsignedSignal is a little-endian unsigned signal at bit zero, offset zero,
// its range starting at zero.
func unsignedSignal(name SignalName, length BitLength, factor, maximum Rational) DBCSignal {
	return DBCSignal{
		Name:      name,
		BitLength: length,
		ByteOrder: LittleEndian,
		Factor:    factor,
		Offset:    ratOf(0, 1),
		Minimum:   ratOf(0, 1),
		Maximum:   maximum,
		Presence:  AlwaysPresent{},
	}
}

// loadOneSignal loads a DBC whose one 8-byte message, 0x100, carries the
// signal, and answers the identifier and length to address it with.
func loadOneSignal(t *testing.T, c *Client, signal DBCSignal) (CANID, DLC) {
	t.Helper()
	id, err := NewStandardID(0x100)
	if err != nil {
		t.Fatalf("NewStandardID: %v", err)
	}
	dlc, err := NewDLC(8)
	if err != nil {
		t.Fatalf("NewDLC: %v", err)
	}
	dbc := DBCDefinition{
		Version: "1.0",
		Messages: []DBCMessage{{
			ID: id, Name: "Msg", DLC: dlc, Sender: "ECU", Signals: []DBCSignal{signal},
		}},
	}
	if _, err := c.ParseDBC(t.Context(), dbc); err != nil {
		t.Fatalf("ParseDBC: %v", err)
	}
	return id, dlc
}

// routeResult is one extraction route's reading of a frame.
type routeResult struct {
	route  string
	result *ExtractionResult
}

// extractOnBothRoutes reads the frame on the binary route, the one
// ExtractSignals takes once a DBC is loaded, and on the JSON route, the
// backend's JSON extraction read by the JSON reply reader.
func extractOnBothRoutes(t *testing.T, c *Client, id CANID, dlc DLC, payload FramePayload) []routeResult {
	t.Helper()
	binaryRoute, err := c.ExtractSignals(t.Context(), id, dlc, payload)
	if err != nil {
		t.Fatalf("ExtractSignals (binary route): %v", err)
	}
	reply, err := c.backend.ExtractSignalsBinary(c.state, id, dlc, []byte(payload))
	if err != nil {
		t.Fatalf("ExtractSignalsBinary (JSON route): %v", err)
	}
	jsonRoute, err := parseExtractionResponse(reply)
	if err != nil {
		t.Fatalf("parseExtractionResponse (JSON route): %v", err)
	}
	return []routeResult{{"binary", binaryRoute}, {"JSON", jsonRoute}}
}

// wideDBCText is a one-message, 8-byte DBC text carrying the given SG_ and
// VAL_ lines.
func wideDBCText(body string) string {
	return "VERSION \"\"\n\nNS_ :\n\nBS_:\n\nBU_: ECU\n\nBO_ 256 M: 8 ECU\n" + body
}

// parseWideText loads the DBC text, failing the test on a refusal.
func parseWideText(t *testing.T, c *Client, text string) DBCDefinition {
	t.Helper()
	parsed, err := c.ParseDBCText(t.Context(), text)
	if err != nil {
		t.Fatalf("ParseDBCText: %v", err)
	}
	return parsed.DBC
}

// skipWithoutLibrary skips a test of an entry outside a session, which the
// runtime TestMain starts answers, when the library is not built.
func skipWithoutLibrary(t *testing.T) {
	t.Helper()
	if findFFILibrary() == "" {
		t.Skip("libaletheia-ffi.so not found; run 'cabal run shake -- build' first")
	}
}

// A 64-bit signal declaring its full range reads its largest raw value,
// 2^64-1, exactly on both extraction routes.
func TestWideNumbers_A64BitRawValueExtractsExactly(t *testing.T) {
	c := newFFIClient(t)
	id, dlc := loadOneSignal(t, c, unsignedSignal("Big", 64, ratOf(1, 1), u64Max))
	want := []SignalValue{{Name: "Big", Value: u64Max}}
	for _, r := range extractOnBothRoutes(t, c, id, dlc, bytes.Repeat([]byte{0xFF}, 8)) {
		if !slices.Equal(r.result.Values, want) || len(r.result.Errors) != 0 {
			t.Errorf("%s route: values %+v, errors %+v; want %+v and no error", r.route, r.result.Values, r.result.Errors, want)
		}
	}
}

// Building a frame from the largest value a 64-bit signal carries, 2^64-1,
// sets every bit.
func TestWideNumbers_AFrameIsBuiltFromA64BitValue(t *testing.T) {
	c := newFFIClient(t)
	id, dlc := loadOneSignal(t, c, unsignedSignal("Big", 64, ratOf(1, 1), u64Max))
	frame, err := c.BuildFrame(t.Context(), id, dlc, []SignalValue{{Name: "Big", Value: u64Max}})
	if err != nil {
		t.Fatalf("BuildFrame: %v", err)
	}
	if want := bytes.Repeat([]byte{0xFF}, 8); !bytes.Equal(frame, want) {
		t.Errorf("frame % x, want % x", []byte(frame), want)
	}
}

// vw_mlb's factor on 16 bits loads and reads its raw values exactly on both
// extraction routes; the reduced numerators at 471, 4097, 65534 and 65535
// pass 64 bits.
func TestWideNumbers_A17PlaceFactorExtractsExactly(t *testing.T) {
	c := newFFIClient(t)
	maximum := new(big.Rat).Mul(vwMLBFactor, new(big.Rat).SetInt64(0xFFFF))
	load := unsignedSignal("Load", 16, rationalOfRat(t, vwMLBFactor), rationalOfRat(t, maximum))
	id, dlc := loadOneSignal(t, c, load)
	for _, raw := range []uint16{0, 1, 255, 470, 471, 4097, 0xFFFE, 0xFFFF} {
		payload := make(FramePayload, 8)
		binary.LittleEndian.PutUint16(payload, raw)
		value := rationalOfRat(t, new(big.Rat).Mul(vwMLBFactor, new(big.Rat).SetInt64(int64(raw))))
		want := []SignalValue{{Name: "Load", Value: value}}
		for _, r := range extractOnBothRoutes(t, c, id, dlc, payload) {
			if !slices.Equal(r.result.Values, want) || len(r.result.Errors) != 0 {
				t.Errorf("raw %d, %s route: values %+v, errors %+v; want %+v and no error", raw, r.route, r.result.Values, r.result.Errors, want)
			}
		}
	}
}

// 2^128 as a signal maximum is refused with the saturated bound refusal: its
// Observed and Limit are both 2^128-1, read at 128 bits, and its message names
// only the limit.
func TestWideNumbers_ANumberPastTheBoundIsRefusedNamingNoNumber(t *testing.T) {
	c := newFFIClient(t)
	text := wideDBCText(fmt.Sprintf(" SG_ S : 0|8@1+ (1,0) [0|%s] \"\" ECU\n", twoTo(128)))
	_, err := c.ParseDBCText(t.Context(), text)
	var bex *InputBoundExceededError
	if !errors.As(err, &bex) {
		t.Fatalf("ParseDBCText: want *InputBoundExceededError, got %v", err)
	}
	if want := "ParseDBCText: signal maximum: rational component magnitude exceeds limit " + rationalBound.String(); bex.Error() != want {
		t.Errorf("message %q, want %q", bex.Error(), want)
	}
	if bex.Observed != rationalBound || bex.Limit != rationalBound {
		t.Errorf("observed %s, limit %s; want both %s", bex.Observed, bex.Limit, rationalBound)
	}
}

// 0.<the 65 digits of 5^92> is 5^27 / 2^65, within the bound, and the factor
// reads back exactly, its denominator past 64 bits.
func TestWideNumbers_AFractionOf65SignificantDigitsThatFitsLoads(t *testing.T) {
	c := newFFIClient(t)
	digits := new(big.Int).Exp(big.NewInt(5), big.NewInt(92), nil).String()
	if len(digits) != 65 {
		t.Fatalf("5^92 has %d digits, want 65", len(digits))
	}
	dbc := parseWideText(t, c, wideDBCText(" SG_ S : 0|8@1+ (0."+digits+",0) [0|1] \"\" ECU\n"))
	want := rationalOfRat(t, new(big.Rat).SetFrac(new(big.Int).Exp(big.NewInt(5), big.NewInt(27), nil), twoTo(65)))
	if got := dbc.Messages[0].Signals[0].Factor; got != want {
		t.Errorf("factor %+v, want %+v", got, want)
	}
}

// m4294967296 on a 40-bit multiplexor loads, and the client reads the
// multiplex value 2^32 back.
func TestWideNumbers_AMultiplexValuePast32BitsLoadsAndReadsBack(t *testing.T) {
	c := newFFIClient(t)
	dbc := parseWideText(t, c, wideDBCText(fmt.Sprintf(" SG_ Mx M : 0|40@1+ (1,0) [0|%d] \"\" ECU\n", uint64(1)<<40-1)+
		" SG_ A m4294967296 : 40|8@1+ (1,0) [0|255] \"\" ECU\n"))
	selected := dbc.Messages[0].Signals[1]
	want := Multiplexed{Multiplexor: "Mx", MultiplexValues: []MultiplexValue{{Lo: 1 << 32}}}
	if !reflect.DeepEqual(selected.Presence, want) {
		t.Errorf("signal %q presence %+v, want %+v", selected.Name, selected.Presence, want)
	}
}

// Tesla's "SNA" at a signed signal's most negative raw value, -32768, loads
// as a value description keyed below zero.
func TestWideNumbers_ANegativeValueDescriptionKeyLoads(t *testing.T) {
	c := newFFIClient(t)
	dbc := parseWideText(t, c, wideDBCText(" SG_ Rpm : 0|16@1- (1,0) [-32768|32767] \"\" ECU\n\n"+
		"VAL_ 256 Rpm -32768 \"SNA\" 0 \"Stopped\" ;\n"))
	rpm := dbc.Messages[0].Signals[0]
	sna := DBCValueEntry{Value: SignMagnitude{Negative: true, Magnitude: Uint128{Lo: 32768}}, Description: "SNA"}
	if !slices.Contains(rpm.ValueDescriptions, sna) {
		t.Errorf("value descriptions %+v, want them to hold %+v", rpm.ValueDescriptions, sna)
	}
}

// A value table's key is signed too, and the client reads the table back.
func TestWideNumbers_ANegativeValueTableKeyLoadsAndReadsBack(t *testing.T) {
	c := newFFIClient(t)
	dbc := parseWideText(t, c, "VERSION \"\"\n\nNS_ :\n\nBS_:\n\nBU_: ECU\n\n"+
		"VAL_TABLE_ Levels -1 \"Below\" 0 \"Zero\" ;\n\n"+
		"BO_ 256 M: 8 ECU\n SG_ S : 0|8@1- (1,0) [-128|127] \"\" ECU\n")
	want := []DBCValueTable{{Name: "Levels", Entries: []DBCValueEntry{
		{Value: SignMagnitude{Negative: true, Magnitude: Uint128{Lo: 1}}, Description: "Below"},
		{Value: SignMagnitude{}, Description: "Zero"},
	}}}
	if !reflect.DeepEqual(dbc.ValueTables, want) {
		t.Errorf("value tables %+v, want %+v", dbc.ValueTables, want)
	}
}

// 2^64-1 microseconds, the largest time bound, is read from text and accepted
// by the metric builders' check.
func TestWideNumbers_ATimeBoundReachesItsLimit(t *testing.T) {
	skipWithoutLibrary(t)
	bound, err := ParseTimeBound(new(big.Int).SetUint64(math.MaxUint64).String())
	if err != nil || bound != (TimeBound{Microseconds: math.MaxUint64}) {
		t.Fatalf("ParseTimeBound(2^64-1) = %+v, %v; want the bound itself", bound, err)
	}
	below, err := Signal("S").LessThan(IntRational(10))
	if err != nil {
		t.Fatalf("LessThan: %v", err)
	}
	if _, err := EventuallyWithin(bound, Atomic{Predicate: below}); err != nil {
		t.Errorf("EventuallyWithin(2^64-1): %v", err)
	}
	if _, err := AlwaysWithin(bound, Atomic{Predicate: below}); err != nil {
		t.Errorf("AlwaysWithin(2^64-1): %v", err)
	}
}

// 2^64 microseconds is past every timestamp: refused with the time bound's
// own limit, its observed size read at 128 bits.
func TestWideNumbers_ATimeBoundPastTheTimestampRangeIsRefused(t *testing.T) {
	skipWithoutLibrary(t)
	past := twoTo(64)
	_, err := ParseTimeBound(past.String())
	var bex *InputBoundExceededError
	if !errors.As(err, &bex) {
		t.Fatalf("ParseTimeBound(2^64): want *InputBoundExceededError, got %v", err)
	}
	limit := Uint128{Lo: math.MaxUint64}
	if bex.Observed != wideOf(t, past) || bex.Limit != limit || bex.Field != "time bound" {
		t.Errorf("observed %s, limit %s, field %q; want %s, %s, %q", bex.Observed, bex.Limit, bex.Field, past, limit, "time bound")
	}
	if want := fmt.Sprintf("time bound: rational component magnitude %s exceeds limit %s", past, limit); bex.Error() != want {
		t.Errorf("message %q, want %q", bex.Error(), want)
	}
}
