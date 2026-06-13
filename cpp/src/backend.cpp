// SPDX-FileCopyrightText: 2025 Nicolas Pelletier
// SPDX-License-Identifier: BSD-2-Clause
// IBackend default implementations — the binary-output endpoints return the
// `BinaryUnsupported` sentinel (so non-FFI backends let Client fall through to
// JSON), and rts_mismatch_info defaults to "no mismatch". The streaming/event
// endpoints have no default (pure-virtual); see backend.hpp.
#include <aletheia/backend.hpp>

#include <cstddef>
#include <expected>
#include <optional>
#include <span>
#include <utility>
#include <vector>

namespace aletheia {

auto IBackend::rts_mismatch_info() const -> std::optional<std::pair<int, int>> {
    return std::nullopt;
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
