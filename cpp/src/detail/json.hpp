// SPDX-FileCopyrightText: 2025 Nicolas Pelletier
// SPDX-License-Identifier: BSD-2-Clause
// Internal JSON serialization/parsing — not part of the public API.
// Tests may include this header to verify JSON round-trips directly.
#pragma once

// The serialize_*/parse_* signatures below use DbcDefinition, LtlFormula,
// FramePayload, FrameResponse, StreamResult, etc. Callers (json_parse.cpp,
// json_serialize.cpp, tests) need those vocabulary types without extra
// direct includes.
#include <aletheia/dbc.hpp>        // IWYU pragma: export
#include <aletheia/error.hpp>      // IWYU pragma: export
#include <aletheia/ltl.hpp>        // IWYU pragma: export
#include <aletheia/response.hpp>   // IWYU pragma: export
#include <aletheia/types.hpp>      // IWYU pragma: export
#include <aletheia/validation.hpp> // IWYU pragma: export

#include <span>
#include <string>
#include <string_view>

namespace aletheia::detail {

// ---------------------------------------------------------------------------
// Serialization (C++ types → JSON command strings)
// ---------------------------------------------------------------------------

auto serialize_parse_dbc(const DbcDefinition& dbc) -> std::string;
auto serialize_parse_dbc_text(std::string_view text) -> std::string;
// Build a successful ParsedDBCResponse JSON wire image from a DBC body.
// Test-only helper: lets MockBackend feed parse_dbc / parse_dbc_text the
// canonical {status, dbc, warnings} envelope without standing up the FFI core.
auto serialize_parsed_dbc_response(const DbcDefinition& dbc) -> std::string;
auto serialize_validate_dbc(const DbcDefinition& dbc) -> std::string;
auto serialize_format_dbc_text(const DbcDefinition& dbc) -> std::string;
auto serialize_set_properties(std::span<const LtlFormula> props) -> std::string;

// ---------------------------------------------------------------------------
// Parsing (JSON response strings → C++ types)
// ---------------------------------------------------------------------------

// Strict: accepts only `"success"` (for parse_dbc, set_properties, start_stream).
auto parse_success(std::string_view input) -> Result<void>;
// Event ack: accepts only `"ack"` for send_error / send_remote. Trace events
// always resolve to `Response.Ack` in Agda (see
// `Aletheia/Protocol/StreamState.agda` handleTraceEvent), so the wire status
// is always "ack". Python and Go enforce the same.
auto parse_event_ack(std::string_view input) -> Result<void>;
auto parse_validation(std::string_view input) -> Result<ValidationResult>;
auto parse_extraction(std::string_view input) -> Result<ExtractionResult>;
auto parse_frame_data(std::string_view input) -> Result<FramePayload>;
auto parse_frame_response(std::string_view input) -> Result<FrameResponse>;
auto parse_stream_result(std::string_view input) -> Result<StreamResult>;
auto parse_dbc_response(std::string_view input) -> Result<DbcDefinition>;
// Parse the response from parseDBC / parseDBCText: `"success"` carrying
// `dbc` (DbcDefinition) and `warnings` (list of ValidationIssue), or
// `"error"` with a typed code.
auto parse_parsed_dbc(std::string_view input) -> Result<ParsedDBC>;
// Parse the response from formatDBCText: `"success"` carrying `text`
// (the .dbc text image), or `"error"` with a typed code.
auto parse_dbc_text_response(std::string_view input) -> Result<std::string>;

// Decode the `aletheia_parse_decimal` wire envelope (raw JSON from
// `detail::parse_decimal_ffi`) into an exact Rational. The kernel is the
// cross-binding single source of truth for decimal→rational (the float
// principle: a decimal is an exact rational, never a float). Branch on
// `status == "error"` BEFORE decoding so the precise `decimal_parse_failed` /
// `decimal_overflow` reason surfaces; on success reuse the existing wire decoder
// (`parse_rational_dict`). Throws `AletheiaException(Validation)` on a parse
// failure / overflow (user input, not a wire fault) — a `std::runtime_error`
// subclass, so the YAML / Excel loaders' `catch (const std::runtime_error&)`
// blocks convert it to a `Result<>` error, while direct callers can branch on
// `.kind()`. Throws `AletheiaException(Protocol)` on a malformed envelope.
auto decode_decimal_response(std::string_view raw) -> Rational;

} // namespace aletheia::detail
