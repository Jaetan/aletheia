// SPDX-FileCopyrightText: 2025 Nicolas Pelletier
// SPDX-License-Identifier: BSD-2-Clause

package aletheia

// The bounds an adversarial input is held to, mirroring src/Aletheia/Limits.agda,
// which owns the numbers; the wire specification states them under Limits in
// docs/architecture/PROTOCOL.md. The kernel enforces every one of them at its
// parser entries. The binding refuses the oversize ones again at the boundary,
// so a payload of a hundred mebibytes is not copied into a C buffer to be
// refused on the far side. A refusal over any of them is a typed
// [InputBoundExceededError] naming the bound, the size observed and the limit.

// The bound kinds, spelling the wire codes boundKindCode renders in the kernel.
const (
	BoundKindInputLengthBytes = "input_length_bytes"
	BoundKindNestingDepth     = "nesting_depth"
	BoundKindArrayCardinality = "array_cardinality"
	BoundKindIdentifierLength = "identifier_length"
	BoundKindStringLength     = "string_length"
	BoundKindAtomCount        = "atom_count"
	BoundKindFrameByteCount   = "frame_byte_count"
	BoundKindPropertyCount    = "property_count"

	// BoundKindRationalComponentMagnitude is a numerator or denominator past
	// the signed 64-bit range the wire carries.
	BoundKindRationalComponentMagnitude = "rational_component_magnitude"
)

// The limits themselves, each the kernel's own value.
const (
	// MaxDBCTextBytes bounds a DBC text input, at 64 mebibytes.
	MaxDBCTextBytes = 64 * 1024 * 1024

	// MaxJSONBytes bounds a JSON payload at the boundary, at 64 mebibytes.
	MaxJSONBytes = 64 * 1024 * 1024

	// MaxNestingDepth bounds how deep JSON objects and arrays may nest.
	MaxNestingDepth = 64

	// MaxMessagesPerFile bounds the messages of one DBC file.
	MaxMessagesPerFile = 10000

	// MaxSignalsPerMessage bounds the signals of one message.
	MaxSignalsPerMessage = 1024

	// MaxAttributesPerFile bounds the attribute definitions and assignments of
	// one file.
	MaxAttributesPerFile = 10000

	// MaxCommentsPerFile bounds the comments of one file.
	MaxCommentsPerFile = 10000

	// MaxNodesPerFile bounds the nodes of one file.
	MaxNodesPerFile = 10000

	// MaxValueTablesPerFile bounds the value tables of one file.
	MaxValueTablesPerFile = 10000

	// MaxValueDescriptionsPerFile bounds the value descriptions of one file,
	// whether they sit in a table or on a signal.
	MaxValueDescriptionsPerFile = 1000000

	// MaxIdentifierLength bounds a DBC identifier, in characters.
	MaxIdentifierLength = 128

	// MaxStringLengthBytes bounds the body of a quoted string, at 64 kibibytes.
	MaxStringLengthBytes = 64 * 1024

	// MaxAtomCountPerProperty bounds the atoms of one property.
	MaxAtomCountPerProperty = 1024

	// MaxPropertiesPerStream bounds the properties one call may install.
	MaxPropertiesPerStream = 1024

	// MaxFrameByteCount bounds a frame payload, at the CAN-FD maximum.
	MaxFrameByteCount = 64

	// MaxRationalComponentMagnitude bounds a numerator or a denominator, at the
	// signed 64-bit range the binary slots and the decimal parser share.
	MaxRationalComponentMagnitude = 9223372036854775807
)
