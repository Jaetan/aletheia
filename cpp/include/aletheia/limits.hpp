// SPDX-FileCopyrightText: 2025 Nicolas Pelletier
// SPDX-License-Identifier: BSD-2-Clause
//
// Adversarial-input bounds — C++ mirror of `Aletheia.Limits` (Agda).
//
// Single source of truth: `src/Aletheia/Limits.agda`; numeric values are
// mirrored here verbatim.  Wire spec: `docs/architecture/PROTOCOL.md § Limits`.
//
// The Aletheia Agda kernel enforces these bounds at every parser entry; this
// header additionally rejects oversize inputs at the FFI boundary so a
// pathological 100 MiB JSON payload is not marshaled across `dlopen`-loaded
// `aletheia_process` only to be rejected on the other side.
//
// Per AGENTS.md universal rule "Adversarial-input bounds at parser surfaces",
// rejection over a bound is a typed `InputBoundExceededError` carrying the
// offending kind, the observed value, and the limit it crossed.  The Python
// (`aletheia.InputBoundExceededError`) and Go (`*aletheia.InputBoundExceededError`)
// bindings expose the equivalent type; keep the three surfaces in sync.
//
// The binding enforces four of these bounds itself before crossing the FFI:
// `max_json_bytes` and `max_frame_byte_count` in ffi_backend.cpp,
// `max_dbc_text_bytes` in the client and the loaders, `max_nesting_depth` in
// the JSON translation units.  The remaining constants are declarations: the
// Agda kernel produces the wire string and the structured triple, and this
// header lets C++ callers identify and compare against them by name.  The
// mirror is held to the Agda module by a probe under probes/ that reads both
// files and compares every bound and every wire string.
#pragma once

#include <cstdint>
#include <string>
#include <string_view>

namespace aletheia {

// ============================================================================
// BOUND KIND CODES
// ============================================================================

// Wire codes — must match `boundKindCode` in `Aletheia.Limits` (Agda).
inline constexpr std::string_view bound_kind_input_length_bytes = "input_length_bytes";
inline constexpr std::string_view bound_kind_nesting_depth = "nesting_depth";
inline constexpr std::string_view bound_kind_array_cardinality = "array_cardinality";
inline constexpr std::string_view bound_kind_identifier_length = "identifier_length";
inline constexpr std::string_view bound_kind_string_length = "string_length";
inline constexpr std::string_view bound_kind_atom_count = "atom_count";
inline constexpr std::string_view bound_kind_frame_byte_count = "frame_byte_count";
inline constexpr std::string_view bound_kind_property_count = "property_count";
inline constexpr std::string_view bound_kind_rational_component_magnitude =
    "rational_component_magnitude";

// ============================================================================
// BOUND CONSTANTS
// ============================================================================

// Total DBC-text input length in bytes (64 MiB).
inline constexpr std::uint64_t max_dbc_text_bytes = 64ULL * 1024 * 1024;

// Total JSON input length in bytes at the FFI boundary (64 MiB).
inline constexpr std::uint64_t max_json_bytes = 64ULL * 1024 * 1024;

// JSON object/array nesting depth.
inline constexpr std::uint64_t max_nesting_depth = 64;

// DBC messages per file.
inline constexpr std::uint64_t max_messages_per_file = 10'000;

// Signals per single DBC message.
inline constexpr std::uint64_t max_signals_per_message = 1024;

// Attribute definitions / assignments per DBC file.
inline constexpr std::uint64_t max_attributes_per_file = 10'000;

// Value-description entries per DBC file (VAL_ + VAL_TABLE_).
inline constexpr std::uint64_t max_value_descriptions_per_file = 1'000'000;

// Comments (CM_), nodes (BU_) and value tables (VAL_TABLE_) per DBC file.
inline constexpr std::uint64_t max_comments_per_file = 10'000;
inline constexpr std::uint64_t max_nodes_per_file = 10'000;
inline constexpr std::uint64_t max_value_tables_per_file = 10'000;

// DBC identifier (signal name, message name, etc.) length in characters.
inline constexpr std::uint64_t max_identifier_length = 128;

// Quoted-string body (comment text, attribute string value) length in bytes.
inline constexpr std::uint64_t max_string_length_bytes = 64ULL * 1024;

// LTL atoms per single property.
inline constexpr std::uint64_t max_atom_count_per_property = 1024;

// Properties per stream.
inline constexpr std::uint64_t max_properties_per_stream = 1024;

// CAN frame payload byte count (CAN-FD maximum).
inline constexpr std::uint64_t max_frame_byte_count = 64;

// Magnitude of a JSON number's numerator and denominator in reduced form: the
// signed 64-bit wire range the binary FFI's rational slots carry.
inline constexpr std::uint64_t max_rational_component_magnitude = 9'223'372'036'854'775'807;

// ============================================================================
// INPUT-BOUND-EXCEEDED ERROR TYPE
// ============================================================================

/// Adversarial-input bound violation, mirroring the Python
/// `aletheia.InputBoundExceededError` and Go `*aletheia.InputBoundExceededError`.
///
/// Stored as a value type (not a derived class of `AletheiaError`) so it can
/// travel inside an `AletheiaError` of kind `InputBoundExceeded` (its
/// `bound_info()`), and so through `Result<T>`, without slicing.  Callers who
/// want the structured fields inspect `bound_info()`; callers who only need
/// the error path use the `AletheiaError` itself.
struct InputBoundExceededError {
    std::string bound_kind; // wire code (one of `bound_kind_*` above)
    std::uint64_t observed; // input value that exceeded the limit
    std::uint64_t limit;    // canonical bound from `Aletheia.Limits`
};

} // namespace aletheia
