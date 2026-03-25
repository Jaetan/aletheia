// Internal JSON serialization/parsing — not part of the public API.
// Tests may include this header to verify JSON round-trips directly.
#pragma once

#include <aletheia/dbc.hpp>
#include <aletheia/error.hpp>
#include <aletheia/ltl.hpp>
#include <aletheia/response.hpp>
#include <aletheia/types.hpp>
#include <aletheia/validation.hpp>

#include <span>
#include <string>
#include <string_view>

namespace aletheia::detail {

// ---------------------------------------------------------------------------
// Serialization (C++ types → JSON command strings)
// ---------------------------------------------------------------------------

auto serialize_parse_dbc(const DbcDefinition& dbc) -> std::string;
auto serialize_validate_dbc(const DbcDefinition& dbc) -> std::string;
auto serialize_format_dbc() -> std::string;
auto serialize_extract_signals(const CanId& id, Dlc dlc, std::span<const std::byte> data)
    -> std::string;
auto serialize_build_frame(const CanId& id, Dlc dlc, std::span<const SignalValue> signals) -> std::string;
auto serialize_update_frame(const CanId& id, Dlc dlc, std::span<const std::byte> data,
                            std::span<const SignalValue> signals) -> std::string;
auto serialize_set_properties(std::span<const LtlFormula> props) -> std::string;
auto serialize_start_stream() -> std::string;
auto serialize_send_frame(Timestamp ts, const CanId& id, Dlc dlc, std::span<const std::byte> data)
    -> std::string;
auto serialize_end_stream() -> std::string;

// ---------------------------------------------------------------------------
// Parsing (JSON response strings → C++ types)
// ---------------------------------------------------------------------------

auto parse_success(std::string_view input) -> Result<void>;
auto parse_validation(std::string_view input) -> Result<ValidationResult>;
auto parse_extraction(std::string_view input) -> Result<ExtractionResult>;
auto parse_frame_data(std::string_view input) -> Result<FramePayload>;
auto parse_frame_response(std::string_view input) -> Result<FrameResponse>;
auto parse_stream_result(std::string_view input) -> Result<StreamResult>;
auto parse_dbc_response(std::string_view input) -> Result<DbcDefinition>;

} // namespace aletheia::detail
