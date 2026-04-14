// IBackend default implementations — fall back to JSON via process().
// MockBackend and other test doubles inherit these defaults.
#include <aletheia/backend.hpp>

#include "detail/json.hpp"

#include <cstddef>
#include <expected>
#include <span>
#include <string>
#include <vector>

namespace aletheia {

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

auto IBackend::build_frame_bin(void* state, const CanId& id, Dlc dlc, SignalInjection signals,
                               std::size_t /*expected_bytes*/)
    -> std::expected<std::vector<std::byte>, AletheiaError> {
    // Default: fall back to JSON path and parse the response.
    auto resp = build_frame_binary(state, id, dlc, signals);
    auto parsed = detail::parse_frame_data(resp);
    if (!parsed)
        return std::unexpected(parsed.error());
    return std::vector<std::byte>(parsed->begin(), parsed->end());
}

auto IBackend::update_frame_bin(void* state, const CanId& id, Dlc dlc,
                                std::span<const std::byte> data, SignalInjection signals,
                                std::size_t /*expected_bytes*/)
    -> std::expected<std::vector<std::byte>, AletheiaError> {
    auto resp = update_frame_binary(state, id, dlc, data, signals);
    auto parsed = detail::parse_frame_data(resp);
    if (!parsed)
        return std::unexpected(parsed.error());
    return std::vector<std::byte>(parsed->begin(), parsed->end());
}

auto IBackend::extract_signals_bin(void* /*state*/, const CanId& /*id*/, Dlc /*dlc*/,
                                   std::span<const std::byte> /*data*/)
    -> std::expected<std::vector<std::byte>, AletheiaError> {
    return std::unexpected(
        AletheiaError{ErrorKind::Protocol, "extract_signals_bin requires FFI backend"});
}

} // namespace aletheia
