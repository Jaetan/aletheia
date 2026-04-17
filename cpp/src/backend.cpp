// SPDX-License-Identifier: BSD-2-Clause
// IBackend default implementations — fall back to JSON via process().
// MockBackend and other test doubles inherit these defaults.
#include <aletheia/backend.hpp>

#include "detail/json.hpp"

#include <cstddef>
#include <expected>
#include <optional>
#include <span>
#include <string>
#include <utility>
#include <vector>

namespace aletheia {

auto IBackend::rts_mismatch_info() const -> std::optional<std::pair<int, int>> {
    return std::nullopt;
}

auto IBackend::send_error_binary(void* state, Timestamp ts) -> std::string {
    return process(state, detail::serialize_send_error(ts));
}

auto IBackend::send_remote_binary(void* state, Timestamp ts, const CanId& id) -> std::string {
    return process(state, detail::serialize_send_remote(ts, id));
}

auto IBackend::start_stream_binary(void* state) -> std::string {
    return process(state, detail::serialize_start_stream());
}

auto IBackend::end_stream_binary(void* state) -> std::string {
    return process(state, detail::serialize_end_stream());
}

auto IBackend::format_dbc_binary(void* state) -> std::string {
    return process(state, detail::serialize_format_dbc());
}

auto IBackend::extract_signals_binary(void* state, const CanId& id, Dlc dlc,
                                      std::span<const std::byte> data) -> std::string {
    return process(state, detail::serialize_extract_signals(id, dlc, data));
}

auto IBackend::build_frame_binary(void* /*state*/, const CanId& /*id*/, Dlc /*dlc*/,
                                  SignalInjection /*signals*/) -> std::string {
    // Cannot reconstruct signal names from indices without DBC context.
    // The Client falls back to JSON serialization via process() when
    // the signal index cache is not populated.  This path should never
    // be reached in normal operation.
    return R"({"status":"error","message":"build_frame_binary requires FFI backend"})";
}

auto IBackend::update_frame_binary(void* /*state*/, const CanId& /*id*/, Dlc /*dlc*/,
                                   std::span<const std::byte> /*data*/, SignalInjection /*signals*/)
    -> std::string {
    return R"({"status":"error","message":"update_frame_binary requires FFI backend"})";
}

auto IBackend::build_frame_bin(void* /*state*/, const CanId& /*id*/, Dlc /*dlc*/,
                               SignalInjection /*signals*/, std::size_t /*expected_bytes*/)
    -> std::expected<std::vector<std::byte>, AletheiaError> {
    // build_frame uses signal indices, which cannot be reconstructed into
    // JSON without the DBC context. Non-FFI backends (MockBackend) cannot
    // service this path — return the BinaryUnsupported sentinel so callers
    // can detect the limitation; Client does not JSON-fall-through here.
    return std::unexpected(
        AletheiaError{ErrorKind::BinaryUnsupported, "binary path not supported by this backend"});
}

auto IBackend::update_frame_bin(void* /*state*/, const CanId& /*id*/, Dlc /*dlc*/,
                                std::span<const std::byte> /*data*/, SignalInjection /*signals*/,
                                std::size_t /*expected_bytes*/)
    -> std::expected<std::vector<std::byte>, AletheiaError> {
    return std::unexpected(
        AletheiaError{ErrorKind::BinaryUnsupported, "binary path not supported by this backend"});
}

auto IBackend::extract_signals_bin(void* /*state*/, const CanId& /*id*/, Dlc /*dlc*/,
                                   std::span<const std::byte> /*data*/)
    -> std::expected<std::vector<std::byte>, AletheiaError> {
    // Sentinel: Client falls through to the JSON path on this kind,
    // mirroring Go's ErrBinaryPathUnsupported contract.
    return std::unexpected(
        AletheiaError{ErrorKind::BinaryUnsupported, "binary path not supported by this backend"});
}

} // namespace aletheia
