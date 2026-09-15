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

// The one sentinel every defaulted binary endpoint returns. The Client falls
// through to the JSON path on it for extract_signals only; build_frame and
// update_frame surface it, since their signal indices cannot be reconstructed
// into JSON without the DBC context. Mirrors Go's ErrBinaryPathUnsupported.
static auto binary_unsupported() -> std::unexpected<AletheiaError> {
    return std::unexpected(
        AletheiaError{ErrorKind::BinaryUnsupported, "binary path not supported by this backend"});
}

auto IBackend::rts_mismatch_info() const -> std::optional<std::pair<int, int>> {
    return std::nullopt;
}

auto IBackend::build_frame_bin(void* /*state*/, const CanId& /*id*/, Dlc /*dlc*/,
                               SignalInjection /*signals*/, std::size_t /*expected_bytes*/)
    -> std::expected<std::vector<std::byte>, AletheiaError> {
    return binary_unsupported();
}

auto IBackend::update_frame_bin(void* /*state*/, const CanId& /*id*/, Dlc /*dlc*/,
                                std::span<const std::byte> /*data*/, SignalInjection /*signals*/,
                                std::size_t /*expected_bytes*/)
    -> std::expected<std::vector<std::byte>, AletheiaError> {
    return binary_unsupported();
}

auto IBackend::extract_signals_bin(void* /*state*/, const CanId& /*id*/, Dlc /*dlc*/,
                                   std::span<const std::byte> /*data*/)
    -> std::expected<std::vector<std::byte>, AletheiaError> {
    return binary_unsupported();
}

} // namespace aletheia
