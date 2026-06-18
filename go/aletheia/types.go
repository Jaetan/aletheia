// SPDX-FileCopyrightText: 2025 Nicolas Pelletier
// SPDX-License-Identifier: BSD-2-Clause

package aletheia

import (
	"fmt"
	"math"
	"time"
)

// FramePayload is a variable-length CAN frame payload (up to 64 bytes for CAN-FD).
type FramePayload []byte

// SignalName identifies a signal within a DBC message.
type SignalName string

// MessageName identifies a message within a DBC definition.
type MessageName string

// NodeName identifies a CAN bus node.
type NodeName string

// Unit is a physical unit string (e.g. "km/h", "degC").
type Unit string

// PhysicalValue is a physical signal reading (e.g. 120.5 km/h).
type PhysicalValue float64

// Rational represents an exact numerator/denominator value.
// Used for DBC signal parameters (factor, offset, min, max) where
// precision beyond float64 matters. Denominator is always positive.
type Rational struct {
	Numerator   int64
	Denominator int64 // always > 0
}

// Float64 converts the rational to a float64.
func (r Rational) Float64() float64 {
	return float64(r.Numerator) / float64(r.Denominator)
}

// IntRational returns an exact [Rational] for an integer literal.
// Useful for predicate construction: “Equals{Value: IntRational(220)}“.
func IntRational(n int64) Rational { return Rational{Numerator: n, Denominator: 1} }

// RationalFromFloat converts a float64 to a [Rational] via 10^9 scaling.
// Integer-valued floats get the exact “n/1“ form; non-integer floats
// fall through to ~9 decimal-digit (≈ ppb) precision shared with the
// FFI signal-value path.
//
// It PANICS on NaN, ±Inf, or a value that overflows int64 when scaled — these
// are programmer errors in the intended use: manual predicate construction with
// compile-time literals (“Equals{Value: aletheia.RationalFromFloat(11.5)}“),
// where the input is known-good (this is the [regexp.MustCompile] convention).
// For exact-precision use prefer “Rational{Numerator: 23, Denominator: 2}“.
// For runtime / user-supplied inputs that may be invalid (e.g. YAML- or
// Excel-loaded checks) use [FloatToRational], which returns an error instead of
// panicking — the check builders ([CheckSignalBuilder] etc.) funnel through it
// for exactly this reason.
func RationalFromFloat(v float64) Rational {
	r, err := FloatToRational(v)
	if err != nil {
		panic("RationalFromFloat: " + err.Error())
	}
	return r
}

// FloatToRational converts a float64 to a [Rational] via 10^9 scaling
// and returns an error for NaN, ±Inf, or values that overflow int64
// when scaled.  Mirrors [strconv.ParseFloat]'s error-returning shape;
// use this at user-input boundaries (e.g. Excel-loaded checks) where
// silently mishandling a bad value would mask data entry mistakes.  See
// [RationalFromFloat] for the panic-on-invalid convenience form used
// for compile-time literals.
//
// Integer-valued floats get the exact “n/1“ form (matching
// [RationalFromFloat]); non-integer floats produce ~9 decimal-digit
// precision via the shared 10^9-scale path.
func FloatToRational(v float64) (Rational, error) {
	if math.IsInf(v, 0) || math.IsNaN(v) {
		return Rational{}, validationError(fmt.Sprintf("cannot convert %v to rational", v))
	}
	if v == math.Trunc(v) && v >= math.MinInt64 && v <= math.MaxInt64 {
		return Rational{Numerator: int64(v), Denominator: 1}, nil
	}
	n, d, err := floatToRational(v)
	if err != nil {
		return Rational{}, err
	}
	return Rational{Numerator: n, Denominator: d}, nil
}

// Timestamp is a point in time, measured in microseconds since trace start.
type Timestamp struct {
	Microseconds int64
}

// Duration returns the Timestamp as a time.Duration.
func (t Timestamp) Duration() time.Duration {
	return time.Duration(t.Microseconds) * time.Microsecond
}

// TimeBound is a time duration for metric temporal operators, in microseconds.
// A zero value is valid and checks only the current time step.
type TimeBound struct {
	Microseconds int64
}

// Duration returns the TimeBound as a time.Duration.
func (t TimeBound) Duration() time.Duration {
	return time.Duration(t.Microseconds) * time.Microsecond
}

// PropertyIndex identifies a property by its position in the property list.
type PropertyIndex uint

// MultiplexValue is a multiplexor selector value.
type MultiplexValue uint32

// Frame bundles all parameters needed to send a CAN frame during streaming.
// Use with [Client.SendFrames] for batch operations.
type Frame struct {
	// Timestamp is the frame's microsecond-precision timestamp.
	Timestamp Timestamp
	// ID is the CAN identifier (11-bit standard or 29-bit extended).
	ID CANID
	// DLC is the data length code (0–8 for CAN 2.0B, 0–15 for CAN-FD).
	DLC DLC
	// Data is the payload — its length must equal DLC.ToBytes().
	Data FramePayload
	// BRS is the CAN-FD Bit Rate Switch bit (ISO 11898-1:2015 §10.4.2):
	// non-nil for CAN-FD frames carrying the bit, nil for CAN 2.0B
	// frames where it does not exist on the wire.  The Aletheia kernel
	// does not consume BRS — it is pass-through metadata for binding
	// consumers and the JSON wire shape (R19P2 cluster 18).
	BRS *bool
	// ESI is the CAN-FD Error State Indicator bit (ISO 11898-1:2015
	// §10.4.3); same semantics + pass-through status as BRS.
	ESI *bool
}

// ByteOrder specifies the byte ordering for a CAN signal.
type ByteOrder int

//go:generate stringer -type=ByteOrder -linecomment -output=byteorder_string.go

const (
	// LittleEndian is Intel byte order (LSB first).
	LittleEndian ByteOrder = iota // little_endian
	// BigEndian is Motorola byte order (MSB first).
	BigEndian // big_endian
)

// BitPosition is a start bit position within a CAN frame.
// Valid domain is 0-511 (64 bytes × 8 bits). Use [NewBitPosition] to create one.
type BitPosition uint16

// MaxBitPosition is the largest valid start-bit position within a CAN-FD frame
// (64 bytes × 8 bits − 1). Consumers building signals from external data can
// use it as the validation boundary before calling [NewBitPosition].
const MaxBitPosition = 511

// NewBitPosition creates a validated BitPosition. Returns an error if v > 511.
func NewBitPosition(v uint16) (BitPosition, error) {
	if v > MaxBitPosition {
		return 0, validationError(fmt.Sprintf("bit position %d exceeds maximum %d", v, MaxBitPosition))
	}
	return BitPosition(v), nil
}

// BitLength is a signal length in bits (1-64). Use [NewBitLength] to create one.
type BitLength uint8

// MaxBitLength is the largest valid signal length in bits for a CAN-FD frame.
// Use it to validate external data before calling [NewBitLength].
const MaxBitLength = 64

// NewBitLength creates a validated BitLength. Returns an error if v < 1 or v > 64.
func NewBitLength(v uint8) (BitLength, error) {
	if v < 1 || v > MaxBitLength {
		return 0, validationError(fmt.Sprintf("bit length %d out of range [1, %d]", v, MaxBitLength))
	}
	return BitLength(v), nil
}

// CANID is a CAN bus identifier. Use [NewStandardID] or [NewExtendedID] to create one.
type CANID interface {
	canID() // sealed
	// Value returns the raw numeric ID.
	Value() uint32
	// IsExtended reports whether this is a 29-bit extended ID.
	IsExtended() bool
}

// MaxStandardID is the largest 11-bit CAN identifier value. Consumers
// validating external data can compare against this before calling
// [NewStandardID].
const MaxStandardID = 1<<11 - 1

// MaxExtendedID is the largest 29-bit CAN identifier value. Use it to
// validate external data before calling [NewExtendedID].
const MaxExtendedID = 1<<29 - 1

// StandardID is an 11-bit CAN identifier (0-2047).
//
// DO NOT RE-RAISE IN REVIEW (R20-GO-A-3.6 — DROP).  Future style sweeps may
// flag the asymmetry between StandardID/ExtendedID exposing values via a
// Value() uint32 method while primitive typedefs (BitPosition uint16,
// BitLength uint8, etc.) use direct conversion (uint16(bp), uint8(bl)).
// Closed DROP after re-audit: the asymmetry is structural, not naming.
// StandardID/ExtendedID wrap an unexported field (enforces NewStandardID
// validation; raw construction is unrepresentable), so Value() is the only
// accessor.  Primitive typedefs carry no validation invariant and don't hide
// state — direct conversion is idiomatic Go (cf. time.Duration → int64).
// Promoting typedefs to wrapper structs would force users to write
// .Value() on every arithmetic site; demoting wrappers to typedefs would
// lose the construction-validation safety.  Revisit only if Go conventions
// shift to require accessor parity across typedef-vs-struct.
type StandardID struct{ value uint16 }

func (id StandardID) canID()           {}
func (id StandardID) Value() uint32    { return uint32(id.value) }
func (id StandardID) IsExtended() bool { return false }
func (id StandardID) String() string   { return fmt.Sprintf("0x%03X", id.value) }

// NewStandardID creates a standard 11-bit CAN ID. Returns an error if v > 2047.
func NewStandardID(v uint16) (StandardID, error) {
	if v > MaxStandardID {
		return StandardID{}, validationError(fmt.Sprintf("standard CAN ID %d exceeds 11-bit range (0-%d)", v, MaxStandardID))
	}
	return StandardID{value: v}, nil
}

// ExtendedID is a 29-bit CAN identifier (0-536870911).
type ExtendedID struct{ value uint32 }

func (id ExtendedID) canID()           {}
func (id ExtendedID) Value() uint32    { return id.value }
func (id ExtendedID) IsExtended() bool { return true }
func (id ExtendedID) String() string   { return fmt.Sprintf("0x%08X", id.value) }

// NewExtendedID creates an extended 29-bit CAN ID. Returns an error if v > 536870911.
func NewExtendedID(v uint32) (ExtendedID, error) {
	if v > MaxExtendedID {
		return ExtendedID{}, validationError(fmt.Sprintf("extended CAN ID %d exceeds 29-bit range (0-%d)", v, MaxExtendedID))
	}
	return ExtendedID{value: v}, nil
}

// DLC is a CAN Data Length Code (0-15). DLC 0-8 map directly to byte counts;
// DLC 9-15 map to 12, 16, 20, 24, 32, 48, 64 bytes (CAN-FD).
type DLC struct{ value uint8 }

// Value returns the raw DLC value.
func (d DLC) Value() uint8 { return d.value }

// ToBytes returns the payload byte count for this DLC.
// DLC 0-8 map directly; 9→12, 10→16, 11→20, 12→24, 13→32, 14→48, 15→64.
func (d DLC) ToBytes() int {
	return dlcTable[d.value]
}

// NewDLC creates a DLC. Returns an error if v > 15.
func NewDLC(v uint8) (DLC, error) {
	if v > 15 {
		return DLC{}, validationError(fmt.Sprintf("DLC %d out of range [0, 15]", v))
	}
	return DLC{value: v}, nil
}

// dlcTable maps DLC values 0-15 to payload byte counts.
var dlcTable = [16]int{0, 1, 2, 3, 4, 5, 6, 7, 8, 12, 16, 20, 24, 32, 48, 64}

// bytesToDlcTable maps valid payload byte counts to DLC codes.
var bytesToDlcTable = map[int]uint8{
	0: 0, 1: 1, 2: 2, 3: 3, 4: 4, 5: 5, 6: 6, 7: 7, 8: 8,
	12: 9, 16: 10, 20: 11, 24: 12, 32: 13, 48: 14, 64: 15,
}

// BytesToDLC converts a payload byte count to a DLC.
// Returns an error if the byte count is not a valid CAN/CAN-FD payload size.
func BytesToDLC(byteCount int) (DLC, error) {
	code, ok := bytesToDlcTable[byteCount]
	if !ok {
		return DLC{}, validationError(fmt.Sprintf("invalid DLC byte count: %d", byteCount))
	}
	return DLC{value: code}, nil
}
