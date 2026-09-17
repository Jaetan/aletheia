// SPDX-FileCopyrightText: 2025 Nicolas Pelletier
// SPDX-License-Identifier: BSD-2-Clause

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

// Unit is a signal's physical unit, as the definition spells it.
type Unit string

// Rational is an exact value, a numerator over a positive denominator. Every
// signal parameter is one, because a scale of a tenth is not a float.
type Rational struct {
	Numerator   int64
	Denominator int64 // always > 0
}

// Float64 converts the rational to a float64.
func (r Rational) Float64() float64 {
	return float64(r.Numerator) / float64(r.Denominator)
}

// IntRational is a whole number as an exact rational, which is how a
// predicate's threshold is written. For a decimal, use [FromDecimal], which
// parses the text exactly; never build one from a float.
func IntRational(n int64) Rational { return Rational{Numerator: n, Denominator: 1} }

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
	// Data is the payload, whose length is the one the length code gives.
	Data FramePayload
	// BRS is the CAN-FD bit-rate-switch bit (ISO 11898-1:2015 section
	// 10.4.2): set for a CAN-FD frame that carries it, absent for a frame
	// of the older format, where the bit does not exist. The kernel does
	// not read it; it crosses to the caller as it came.
	BRS *bool
	// ESI is the CAN-FD error-state-indicator bit (section 10.4.3), which
	// crosses the same way.
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

// BitPosition is where a signal starts within a frame. Build one with
// [NewBitPosition], which refuses a position past the last bit of the largest
// frame.
type BitPosition uint16

// MaxBitPosition is the last bit of the largest frame, for a caller checking
// its own data before building one.
const MaxBitPosition = 511

// NewBitPosition creates a validated BitPosition. Returns an error if v > 511.
func NewBitPosition(v uint16) (BitPosition, error) {
	if v > MaxBitPosition {
		return 0, validationError(fmt.Sprintf("bit position %d exceeds maximum %d", v, MaxBitPosition))
	}
	return BitPosition(v), nil
}

// BitLength is how many bits a signal occupies. Build one with [NewBitLength].
type BitLength uint16

// MaxBitLength is every bit of the largest frame: the ceiling no signal can
// exceed whatever message it sits in. Whether a signal fits the message it is
// declared in is the kernel's decision when the definition is read.
const MaxBitLength = 512

// NewBitLength creates a validated BitLength. Returns an error if v < 1 or v > 512.
func NewBitLength(v uint16) (BitLength, error) {
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

// StandardID is an eleven-bit identifier.
//
// It hides its number behind a method where the plainer types above are read
// by conversion, and the difference is the invariant: an identifier that
// cannot be built without being checked has to hide the field the check
// guards, while a position or a length carries no invariant and reads better
// converted, as a duration does.
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

// DLC is a frame's length code. The first nine codes are the byte counts
// themselves; the rest name the larger payloads CAN-FD adds.
type DLC struct{ value uint8 }

// Value returns the raw DLC value.
func (d DLC) Value() uint8 { return d.value }

// ToBytes is the payload length this code stands for.
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

// dlcTable is the payload length of each code, and the only place either
// direction is written.
var dlcTable = [16]int{0, 1, 2, 3, 4, 5, 6, 7, 8, 12, 16, 20, 24, 32, 48, 64}

// bytesToDlcTable is that table read backwards, built from it rather than
// written again, so the two directions cannot disagree. Each length appears
// once, which is what makes the inversion a function.
var bytesToDlcTable = func() map[int]uint8 {
	m := make(map[int]uint8, len(dlcTable))
	for code, length := range dlcTable {
		m[length] = uint8(code)
	}
	return m
}()

// BytesToDLC is the code for a payload length, refusing a length no frame has.
func BytesToDLC(byteCount int) (DLC, error) {
	code, ok := bytesToDlcTable[byteCount]
	if !ok {
		return DLC{}, validationError(fmt.Sprintf("invalid DLC byte count: %d", byteCount))
	}
	return DLC{value: code}, nil
}
