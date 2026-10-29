// SPDX-FileCopyrightText: 2025 Nicolas Pelletier
// SPDX-License-Identifier: BSD-2-Clause
// IBackend default implementations, plus the out-of-line members of
// BackendState and SignalInjection.
// The binary-output endpoints return the
// `BinaryUnsupported` sentinel (so non-FFI backends let Client fall through to
// JSON), and rts_mismatch_info defaults to "no mismatch". The streaming/event
// endpoints have no default (pure-virtual); see backend.hpp.
#include <aletheia/backend.hpp>

#include "detail/ffi_logic.hpp"

#include <cstddef>
#include <cstdint>
#include <expected>
#include <format>
#include <optional>
#include <span>
#include <string>
#include <utility>
#include <vector>

namespace aletheia {

// BackendState's out-of-line members: each needs IBackend complete, and the
// vtable is emitted in this translation unit anyway.
void BackendState::release() noexcept {
    if (backend_ != nullptr && state_ != nullptr)
        backend_->close(state_);
    backend_ = nullptr;
    state_ = nullptr;
}

BackendState::~BackendState() {
    release();
}

BackendState::BackendState(BackendState&& other) noexcept
    : backend_(std::exchange(other.backend_, nullptr))
    , state_(std::exchange(other.state_, nullptr)) {
}

auto BackendState::operator=(BackendState&& other) noexcept -> BackendState& {
    if (this != &other) {
        release();
        backend_ = std::exchange(other.backend_, nullptr);
        state_ = std::exchange(other.state_, nullptr);
    }
    return *this;
}

// SignalInjection refuses the two shapes the FFI would read past: three arrays
// that are not the same length, and a length its 32-bit count cannot carry.
auto SignalInjection::create(std::span<std::uint32_t const> indices,
                             std::span<std::int64_t const> numerators,
                             std::span<std::int64_t const> denominators)
    -> Result<SignalInjection> {
    if (indices.size() != numerators.size() || indices.size() != denominators.size())
        return detail::validation_refusal(
            std::format("signal injection arrays differ in length: {} indices, {} numerators, "
                        "{} denominators",
                        indices.size(), numerators.size(), denominators.size()));
    if (auto refusal = detail::wire_count_refusal(indices.size()))
        return detail::validation_refusal(std::move(refusal).value());
    SignalInjection block;
    block.indices_ = indices;
    block.numerators_ = numerators;
    block.denominators_ = denominators;
    return block;
}

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

auto IBackend::build_frame_bin(BackendState const& /*state*/, CanId const& /*id*/, Dlc /*dlc*/,
                               SignalInjection /*signals*/, std::size_t /*expected_bytes*/)
    -> std::expected<std::vector<std::byte>, AletheiaError> {
    return binary_unsupported();
}

auto IBackend::update_frame_bin(BackendState const& /*state*/, CanId const& /*id*/, Dlc /*dlc*/,
                                std::span<std::byte const> /*data*/, SignalInjection /*signals*/,
                                std::size_t /*expected_bytes*/)
    -> std::expected<std::vector<std::byte>, AletheiaError> {
    return binary_unsupported();
}

auto IBackend::extract_signals_bin(BackendState const& /*state*/, CanId const& /*id*/, Dlc /*dlc*/,
                                   std::span<std::byte const> /*data*/)
    -> std::expected<std::vector<std::byte>, AletheiaError> {
    return binary_unsupported();
}

} // namespace aletheia
