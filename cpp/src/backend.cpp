// IBackend default implementations — fall back to JSON via process().
// MockBackend and other test doubles inherit these defaults.
#include <aletheia/backend.hpp>

#include "detail/json.hpp"

namespace aletheia {

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

auto IBackend::build_frame_binary(void* state, const CanId& id, Dlc dlc,
                                  std::uint32_t /*num_signals*/,
                                  const std::uint32_t* /*indices*/,
                                  const std::int64_t* /*numerators*/,
                                  const std::int64_t* /*denominators*/) -> std::string {
    // Cannot reconstruct signal names from indices without DBC context.
    // The Client falls back to JSON serialization via process() when
    // the signal index cache is not populated.  This path should never
    // be reached in normal operation.
    (void)state;
    (void)id;
    (void)dlc;
    return R"({"status":"error","error":"build_frame_binary requires FFI backend"})";
}

auto IBackend::update_frame_binary(void* state, const CanId& id, Dlc dlc,
                                   std::span<const std::byte> /*data*/,
                                   std::uint32_t /*num_signals*/,
                                   const std::uint32_t* /*indices*/,
                                   const std::int64_t* /*numerators*/,
                                   const std::int64_t* /*denominators*/) -> std::string {
    (void)state;
    (void)id;
    (void)dlc;
    return R"({"status":"error","error":"update_frame_binary requires FFI backend"})";
}

auto IBackend::build_frame_bin(void* state, const CanId& id, Dlc dlc,
                               std::uint32_t num_signals,
                               const std::uint32_t* indices,
                               const std::int64_t* numerators,
                               const std::int64_t* denominators,
                               std::size_t expected_bytes)
    -> std::expected<std::vector<std::byte>, AletheiaError> {
    // Default: fall back to JSON path and parse the response.
    auto resp = build_frame_binary(state, id, dlc, num_signals, indices, numerators, denominators);
    auto parsed = detail::parse_frame_data(resp);
    if (!parsed)
        return std::unexpected(parsed.error());
    return std::vector<std::byte>(parsed->begin(), parsed->end());
}

auto IBackend::update_frame_bin(void* state, const CanId& id, Dlc dlc,
                                std::span<const std::byte> data,
                                std::uint32_t num_signals,
                                const std::uint32_t* indices,
                                const std::int64_t* numerators,
                                const std::int64_t* denominators,
                                std::size_t expected_bytes)
    -> std::expected<std::vector<std::byte>, AletheiaError> {
    auto resp = update_frame_binary(state, id, dlc, data, num_signals, indices, numerators,
                                    denominators);
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
