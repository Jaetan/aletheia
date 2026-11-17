// SPDX-FileCopyrightText: 2025 Nicolas Pelletier
// SPDX-License-Identifier: BSD-2-Clause

//! The kernel's bound kinds, each the wire code `boundKindCode` renders in `Aletheia.Limits`.

/// Total input length in bytes, at a parser entry.
pub const BOUND_KIND_INPUT_LENGTH_BYTES: &str = "input_length_bytes";
/// JSON nesting depth, object and array containment.
pub const BOUND_KIND_NESTING_DEPTH: &str = "nesting_depth";
/// The length of one list, such as a DBC's messages, a message's signals or senders.
pub const BOUND_KIND_ARRAY_CARDINALITY: &str = "array_cardinality";
/// The length of an identifier, such as a DBC's signal or message name.
pub const BOUND_KIND_IDENTIFIER_LENGTH: &str = "identifier_length";
/// The length of a DBC text field, such as a comment or a string attribute value.
pub const BOUND_KIND_STRING_LENGTH: &str = "string_length";
/// The atoms of one property.
pub const BOUND_KIND_ATOM_COUNT: &str = "atom_count";
/// The properties one `set_properties` call submits.
pub const BOUND_KIND_PROPERTY_COUNT: &str = "property_count";
/// A number past its field's limit, such as a rational's numerator past 2^128-1.
pub const BOUND_KIND_RATIONAL_COMPONENT_MAGNITUDE: &str = "rational_component_magnitude";
