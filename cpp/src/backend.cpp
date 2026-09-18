// SPDX-FileCopyrightText: 2025 Nicolas Pelletier
// SPDX-License-Identifier: BSD-2-Clause
// IBackend default implementations, plus the out-of-line members of
// BackendState and SignalInjection.
// The binary-output endpoints return the
// `BinaryUnsupported` sentinel (so non-FFI backends let Client fall through to
// JSON), and rts_mismatch_info defaults to "no mismatch". The streaming/event
// endpoints have no default (pure-virtual); see backend.hpp.
#include <aletheia/backend.hpp>

#include <cstddef>
#include <cstdint>
#include <exception>
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
//
// release swallows, because it runs from the destructor and from a noexcept
// move assignment, where a throw would terminate the program. The FFI close
// path allocates nothing, but another backend may throw.
void BackendState::release() noexcept {
    if (backend_ != nullptr && state_ != nullptr) {
        try {
            backend_->close(state_);
        } catch (...) {
            static_cast<void>(std::current_exception());
        }
    }
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
auto SignalInjection::create(std::span<const std::uint32_t> indices,
                             std::span<const std::int64_t> numerators,
                             std::span<const std::int64_t> denominators)
    -> std::expected<SignalInjection, std::string> {
    if (indices.size() != numerators.size() || indices.size() != denominators.size())
        return std::unexpected(
            std::format("signal injection arrays differ in length: {} indices, {} numerators, "
                        "{} denominators",
                        indices.size(), numerators.size(), denominators.size()));
    // Held by reading: a block past the wire's width needs more memory than
    // a test can allocate.
    if (!std::in_range<std::uint32_t>(indices.size()))
        return std::unexpected(
            std::format("signal injection carries {} values, more than the wire's count holds",
                        indices.size()));
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

auto IBackend::build_frame_bin(const BackendState& /*state*/, const CanId& /*id*/, Dlc /*dlc*/,
                               SignalInjection /*signals*/, std::size_t /*expected_bytes*/)
    -> std::expected<std::vector<std::byte>, AletheiaError> {
    return binary_unsupported();
}

auto IBackend::update_frame_bin(const BackendState& /*state*/, const CanId& /*id*/, Dlc /*dlc*/,
                                std::span<const std::byte> /*data*/, SignalInjection /*signals*/,
                                std::size_t /*expected_bytes*/)
    -> std::expected<std::vector<std::byte>, AletheiaError> {
    return binary_unsupported();
}

auto IBackend::extract_signals_bin(const BackendState& /*state*/, const CanId& /*id*/, Dlc /*dlc*/,
                                   std::span<const std::byte> /*data*/)
    -> std::expected<std::vector<std::byte>, AletheiaError> {
    return binary_unsupported();
}

} // namespace aletheia
