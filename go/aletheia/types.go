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

// ScaleFactor is a DBC signal scaling factor.
type ScaleFactor float64

// ScaleOffset is a DBC signal scaling offset.
type ScaleOffset float64

// Delta is an absolute change magnitude for ChangedBy predicates.
type Delta float64

// Timestamp is a point in time, measured in microseconds since trace start.
type Timestamp struct {
	Microseconds int64
}

// Duration returns the Timestamp as a time.Duration.
func (t Timestamp) Duration() time.Duration {
	return time.Duration(t.Microseconds) * time.Microsecond
}

// PropertyIndex identifies a property by its position in the property list.
type PropertyIndex uint

// MultiplexValue is a multiplexor selector value.
type MultiplexValue uint32

// ByteOrder specifies the byte ordering for a CAN signal.
type ByteOrder int

const (
	// LittleEndian is Intel byte order (LSB first).
	LittleEndian ByteOrder = iota
	// BigEndian is Motorola byte order (MSB first).
	BigEndian
)

// BitPosition is a start bit position within a CAN frame (0-63).
type BitPosition uint16

// BitLength is a signal length in bits (1-64).
type BitLength uint8

// CanID is a CAN bus identifier. Use [NewStandardID] or [NewExtendedID] to create one.
type CanID interface {
	canID() // sealed
	// Value returns the raw numeric ID.
	Value() uint32
	// IsExtended reports whether this is a 29-bit extended ID.
	IsExtended() bool
}

// StandardID is an 11-bit CAN identifier (0-2047).
type StandardID struct{ value uint16 }

func (id StandardID) canID()           {}
func (id StandardID) Value() uint32    { return uint32(id.value) }
func (id StandardID) IsExtended() bool { return false }
func (id StandardID) String() string   { return fmt.Sprintf("0x%03X", id.value) }

// NewStandardID creates a standard 11-bit CAN ID. Returns an error if v > 2047.
func NewStandardID(v uint16) (StandardID, error) {
	if v > 2047 {
		return StandardID{}, validationError(fmt.Sprintf("standard CAN ID %d exceeds 11-bit range (0-2047)", v))
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
	if v > 536870911 {
		return ExtendedID{}, validationError(fmt.Sprintf("extended CAN ID %d exceeds 29-bit range (0-536870911)", v))
	}
	return ExtendedID{value: v}, nil
}

// DLC is a CAN Data Length Code (0-15). DLC 0-8 map directly to byte counts;
// DLC 9-15 map to 12, 16, 20, 24, 32, 48, 64 bytes (CAN-FD).
type DLC struct{ value uint8 }

// Value returns the raw DLC value.
func (d DLC) Value() uint8 { return d.value }

// ToBytes returns the payload byte count for this DLC.
func (d DLC) ToBytes() int {
	return DlcToBytes(d)
}

// NewDLC creates a DLC. Returns an error if v > 15.
func NewDLC(v uint8) (DLC, error) {
	if v > 15 {
		return DLC{}, validationError(fmt.Sprintf("DLC %d exceeds CAN-FD range (0-15)", v))
	}
	return DLC{value: v}, nil
}

// dlcTable maps DLC values 0-15 to payload byte counts.
var dlcTable = [16]int{0, 1, 2, 3, 4, 5, 6, 7, 8, 12, 16, 20, 24, 32, 48, 64}

// DlcToBytes returns the payload byte count for a DLC value.
// DLC 0-8 map directly; 9→12, 10→16, 11→20, 12→24, 13→32, 14→48, 15→64.
func DlcToBytes(dlc DLC) int {
	return dlcTable[dlc.value]
}
