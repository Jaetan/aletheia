package aletheia

import (
	"fmt"
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

// Delta is a signed change threshold for ChangedBy predicates.
// Positive: curr - prev >= delta; negative: curr - prev <= delta.
type Delta float64

// Tolerance is an absolute tolerance for StableWithin predicates.
type Tolerance float64

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
	Timestamp Timestamp
	ID        CanID
	DLC       DLC
	Data      FramePayload
}

// ByteOrder specifies the byte ordering for a CAN signal.
type ByteOrder int

const (
	// LittleEndian is Intel byte order (LSB first).
	LittleEndian ByteOrder = iota
	// BigEndian is Motorola byte order (MSB first).
	BigEndian
)

// String returns the protocol wire name: "little_endian" or "big_endian".
func (b ByteOrder) String() string {
	switch b {
	case LittleEndian:
		return "little_endian"
	case BigEndian:
		return "big_endian"
	default:
		return "unknown"
	}
}

// BitPosition is a start bit position within a CAN frame.
// Valid domain is 0-511 (64 bytes × 8 bits). Use [NewBitPosition] to create one.
type BitPosition uint16

const maxBitPosition = 511 // 64 bytes × 8 bits − 1

// NewBitPosition creates a validated BitPosition. Returns an error if v > 511.
func NewBitPosition(v uint16) (BitPosition, error) {
	if v > maxBitPosition {
		return 0, validationError(fmt.Sprintf("bit position %d exceeds maximum %d", v, maxBitPosition))
	}
	return BitPosition(v), nil
}

// BitLength is a signal length in bits (1-64). Use [NewBitLength] to create one.
type BitLength uint8

const maxBitLength = 64 // max signal bits in a CAN frame

// NewBitLength creates a validated BitLength. Returns an error if v < 1 or v > 64.
func NewBitLength(v uint8) (BitLength, error) {
	if v < 1 || v > maxBitLength {
		return 0, validationError(fmt.Sprintf("bit length %d out of range [1, %d]", v, maxBitLength))
	}
	return BitLength(v), nil
}

// CanID is a CAN bus identifier. Use [NewStandardID] or [NewExtendedID] to create one.
type CanID interface {
	canID() // sealed
	// Value returns the raw numeric ID.
	Value() uint32
	// IsExtended reports whether this is a 29-bit extended ID.
	IsExtended() bool
}

const (
	maxStandardID = 1<<11 - 1 // 11-bit CAN ID
	maxExtendedID = 1<<29 - 1 // 29-bit CAN ID
)

// StandardID is an 11-bit CAN identifier (0-2047).
type StandardID struct{ value uint16 }

func (id StandardID) canID()           {}
func (id StandardID) Value() uint32    { return uint32(id.value) }
func (id StandardID) IsExtended() bool { return false }
func (id StandardID) String() string   { return fmt.Sprintf("0x%03X", id.value) }

// NewStandardID creates a standard 11-bit CAN ID. Returns an error if v > 2047.
func NewStandardID(v uint16) (StandardID, error) {
	if v > maxStandardID {
		return StandardID{}, validationError(fmt.Sprintf("standard CAN ID %d exceeds 11-bit range (0-%d)", v, maxStandardID))
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
	if v > maxExtendedID {
		return ExtendedID{}, validationError(fmt.Sprintf("extended CAN ID %d exceeds 29-bit range (0-%d)", v, maxExtendedID))
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
