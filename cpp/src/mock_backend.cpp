// SPDX-FileCopyrightText: 2025 Nicolas Pelletier
// SPDX-License-Identifier: BSD-2-Clause
// make_mock_backend(): the public test double.
#include <aletheia/backend.hpp>

#include <cstddef>
#include <expected>
#include <memory>
#include <optional>
#include <span>
#include <string>
#include <string_view>
#include <vector>

namespace aletheia {
namespace {

// The wire's acknowledgement, which is what each of these operations returns on
// success when it carries no payload of its own.
constexpr std::string_view k_ack = R"({"status":"ack"})";

// A backend that answers every call the same way, with no queue to fill and no
// mode to select.
//
// The configurable double lives in a test-internal header that an installed
// consumer cannot include, so a public backend that refused until its queue was
// filled would be one such a consumer could never call. This one is the fixed
// canned-acknowledgement backend the public surface has always been described
// as shipping.
//
// Fixed means fixed: it records nothing and decides nothing, so there is no
// branch here for a test to cover or a sweep to mutate.
class CannedAckBackend : public IBackend {
    static inline char sentinel = 0;

public:
    auto init() -> BackendState override { return BackendState{*this, &sentinel}; }

    auto process(const BackendState& /*state*/, std::string_view /*input*/)
        -> std::string override {
        return std::string{k_ack};
    }

    auto send_frame_binary(const BackendState& /*state*/, Timestamp /*ts*/, const CanId& /*id*/,
                           Dlc /*dlc*/, std::span<const std::byte> /*data*/,
                           std::optional<bool> /*brs*/, std::optional<bool> /*esi*/)
        -> std::string override {
        return std::string{k_ack};
    }

    auto send_error_binary(const BackendState& /*state*/, Timestamp /*ts*/)
        -> std::string override {
        return std::string{k_ack};
    }

    auto send_remote_binary(const BackendState& /*state*/, Timestamp /*ts*/, const CanId& /*id*/)
        -> std::string override {
        return std::string{k_ack};
    }

    auto start_stream_binary(const BackendState& /*state*/) -> std::string override {
        return std::string{k_ack};
    }

    auto end_stream_binary(const BackendState& /*state*/) -> std::string override {
        return std::string{k_ack};
    }

    auto format_dbc_binary(const BackendState& /*state*/) -> std::string override {
        return std::string{k_ack};
    }

    auto extract_signals_binary(const BackendState& /*state*/, const CanId& /*id*/, Dlc /*dlc*/,
                                std::span<const std::byte> /*data*/) -> std::string override {
        return std::string{k_ack};
    }

    // A frame request is answered with the payload the caller asked for,
    // zero-filled: the one response of the right shape that invents no signal
    // value. The base class's default would refuse instead, and the client
    // forwards these results without a JSON fallback.
    [[nodiscard]] auto build_frame_bin(const BackendState& /*state*/, const CanId& /*id*/,
                                       Dlc /*dlc*/, SignalInjection /*signals*/,
                                       std::size_t expected_bytes)
        -> std::expected<std::vector<std::byte>, AletheiaError> override {
        return std::vector<std::byte>(expected_bytes);
    }

    [[nodiscard]] auto update_frame_bin(const BackendState& /*state*/, const CanId& /*id*/,
                                        Dlc /*dlc*/, std::span<const std::byte> /*data*/,
                                        SignalInjection /*signals*/, std::size_t expected_bytes)
        -> std::expected<std::vector<std::byte>, AletheiaError> override {
        return std::vector<std::byte>(expected_bytes);
    }

protected:
    // The state is a static sentinel, so there is nothing to release.
    void close(void* /*state*/) override {}
};

} // namespace

auto make_mock_backend() -> std::unique_ptr<IBackend> {
    return std::make_unique<CannedAckBackend>();
}

} // namespace aletheia
