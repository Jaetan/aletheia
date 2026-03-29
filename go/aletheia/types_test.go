package aletheia_test

import (
	"testing"
	"time"

	"github.com/aletheia-automotive/aletheia-go/aletheia"
)

func TestStandardID_Range(t *testing.T) {
	_, err := aletheia.NewStandardID(2048)
	if err == nil {
		t.Error("expected error for standard ID > 2047")
	}

	sid, err := aletheia.NewStandardID(2047)
	if err != nil {
		t.Fatalf("expected success for 2047: %v", err)
	}
	if sid.Value() != 2047 {
		t.Errorf("expected 2047, got %d", sid.Value())
	}
	if sid.IsExtended() {
		t.Error("standard ID should not be extended")
	}
}

func TestExtendedID_Range(t *testing.T) {
	_, err := aletheia.NewExtendedID(536870912)
	if err == nil {
		t.Error("expected error for extended ID > 536870911")
	}

	eid, err := aletheia.NewExtendedID(536870911)
	if err != nil {
		t.Fatalf("expected success for 536870911: %v", err)
	}
	if eid.Value() != 536870911 {
		t.Errorf("expected 536870911, got %d", eid.Value())
	}
	if !eid.IsExtended() {
		t.Error("extended ID should be extended")
	}
}

func TestDLC_Range(t *testing.T) {
	_, err := aletheia.NewDLC(16)
	if err == nil {
		t.Error("expected error for DLC > 15")
	}

	dlc, err := aletheia.NewDLC(15)
	if err != nil {
		t.Fatalf("expected success for 15: %v", err)
	}
	if dlc.Value() != 15 {
		t.Errorf("expected 15, got %d", dlc.Value())
	}
	if dlc.ToBytes() != 64 {
		t.Errorf("DLC 15 should map to 64 bytes, got %d", dlc.ToBytes())
	}

	// Verify CAN-FD DLC mapping
	dlcMap := map[uint8]int{
		0: 0, 1: 1, 2: 2, 3: 3, 4: 4, 5: 5, 6: 6, 7: 7, 8: 8,
		9: 12, 10: 16, 11: 20, 12: 24, 13: 32, 14: 48, 15: 64,
	}
	for v, expectedBytes := range dlcMap {
		d, err := aletheia.NewDLC(v)
		if err != nil {
			t.Fatalf("NewDLC(%d): %v", v, err)
		}
		if d.ToBytes() != expectedBytes {
			t.Errorf("DLC %d: expected %d bytes, got %d", v, expectedBytes, d.ToBytes())
		}
	}
}

func TestTimestamp_Duration(t *testing.T) {
	ts := aletheia.Timestamp{Microseconds: 1_000_000}
	if ts.Duration().Seconds() != 1.0 {
		t.Errorf("expected 1s, got %v", ts.Duration())
	}
}

func TestTimeBound_Duration(t *testing.T) {
	tb := aletheia.TimeBound{Microseconds: 5_000_000}
	if tb.Duration() != 5*time.Second {
		t.Errorf("expected 5s, got %v", tb.Duration())
	}
	zero := aletheia.TimeBound{Microseconds: 0}
	if zero.Duration() != 0 {
		t.Errorf("expected 0, got %v", zero.Duration())
	}
}

func TestVerdictString(t *testing.T) {
	if aletheia.Holds.String() != "holds" {
		t.Errorf("expected 'holds', got %q", aletheia.Holds.String())
	}
	if aletheia.Fails.String() != "fails" {
		t.Errorf("expected 'fails', got %q", aletheia.Fails.String())
	}
}

func TestConstructorErrorType(t *testing.T) {
	_, err := aletheia.NewStandardID(2048)
	if err == nil {
		t.Fatal("expected error")
	}
	aErr, ok := err.(*aletheia.Error)
	if !ok {
		t.Fatalf("expected *aletheia.Error, got %T", err)
	}
	if aErr.Kind != aletheia.ErrValidation {
		t.Errorf("expected ErrValidation, got %s", aErr.Kind)
	}
}

func TestByteOrderString(t *testing.T) {
	if got := aletheia.LittleEndian.String(); got != "little_endian" {
		t.Errorf("LittleEndian.String() = %q, want %q", got, "little_endian")
	}
	if got := aletheia.BigEndian.String(); got != "big_endian" {
		t.Errorf("BigEndian.String() = %q, want %q", got, "big_endian")
	}
}

func TestIssueSeverityString(t *testing.T) {
	if got := aletheia.SeverityError.String(); got != "error" {
		t.Errorf("SeverityError.String() = %q, want %q", got, "error")
	}
	if got := aletheia.SeverityWarning.String(); got != "warning" {
		t.Errorf("SeverityWarning.String() = %q, want %q", got, "warning")
	}
}

func TestStandardID_String(t *testing.T) {
	tests := []struct {
		id   uint16
		want string
	}{
		{0x123, "0x123"},
		{0x001, "0x001"},
		{0x000, "0x000"},
		{0x7FF, "0x7FF"},
	}
	for _, tt := range tests {
		sid, err := aletheia.NewStandardID(tt.id)
		if err != nil {
			t.Fatalf("NewStandardID(%d): %v", tt.id, err)
		}
		if got := sid.String(); got != tt.want {
			t.Errorf("StandardID(%d).String() = %q, want %q", tt.id, got, tt.want)
		}
	}
}

func TestExtendedID_String(t *testing.T) {
	tests := []struct {
		id   uint32
		want string
	}{
		{0x18FEF100, "0x18FEF100"},
		{0x00000001, "0x00000001"},
		{0x00000000, "0x00000000"},
		{0x1FFFFFFF, "0x1FFFFFFF"},
	}
	for _, tt := range tests {
		eid, err := aletheia.NewExtendedID(tt.id)
		if err != nil {
			t.Fatalf("NewExtendedID(%d): %v", tt.id, err)
		}
		if got := eid.String(); got != tt.want {
			t.Errorf("ExtendedID(%d).String() = %q, want %q", tt.id, got, tt.want)
		}
	}
}

func TestImpliesConstructor(t *testing.T) {
	a := aletheia.Atomic{Predicate: aletheia.LessThan{Signal: "Speed", Value: 220}}
	b := aletheia.Atomic{Predicate: aletheia.GreaterThan{Signal: "RPM", Value: 500}}
	f := aletheia.Implies(a, b)

	or, ok := f.(aletheia.Or)
	if !ok {
		t.Fatalf("expected Or, got %T", f)
	}
	notA, ok := or.Left.(aletheia.Not)
	if !ok {
		t.Fatalf("expected Not on left, got %T", or.Left)
	}
	if _, ok := notA.Inner.(aletheia.Atomic); !ok {
		t.Fatalf("expected Atomic inside Not, got %T", notA.Inner)
	}
	if _, ok := or.Right.(aletheia.Atomic); !ok {
		t.Fatalf("expected Atomic on right, got %T", or.Right)
	}
}
