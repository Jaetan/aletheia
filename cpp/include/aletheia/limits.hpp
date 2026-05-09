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
// bindings expose the equivalent type; keep the three surfaces in sync per
// `feedback_cross_language_parity.md`.
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

// DBC identifier (signal name, message name, etc.) length in characters.
inline constexpr std::uint64_t max_identifier_length = 128;

// Quoted-string body (comment text, attribute string value) length in bytes.
inline constexpr std::uint64_t max_string_length_bytes = 64ULL * 1024;

// LTL atoms per single property.
inline constexpr std::uint64_t max_atom_count_per_property = 1024;

// CAN frame payload byte count (CAN-FD maximum).
inline constexpr std::uint64_t max_frame_byte_count = 64;

// ============================================================================
// INPUT-BOUND-EXCEEDED ERROR TYPE
// ============================================================================

/// Adversarial-input bound violation, mirroring the Python
/// `aletheia.InputBoundExceededError` and Go `*aletheia.InputBoundExceededError`.
///
/// Stored as a value type (not a derived class of `AletheiaError`) so it can
/// flow uniformly through `Result<T> = std::expected<T, AletheiaError>` after
/// `to_aletheia_error()` lowering, without slicing.  Callers who want the
/// structured fields construct or inspect this struct directly at the
/// rejection site; callers who only need the error path use the lowered
/// `AletheiaError` form.
struct InputBoundExceededError {
    std::string bound_kind; // wire code (one of `bound_kind_*` above)
    std::uint64_t observed; // input value that exceeded the limit
    std::uint64_t limit;    // canonical bound from `Aletheia.Limits`
};

} // namespace aletheia
