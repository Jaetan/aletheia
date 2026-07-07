// SPDX-FileCopyrightText: 2025 Nicolas Pelletier
// SPDX-License-Identifier: BSD-2-Clause
// Configurable mock backend for testing.
// Tests include this header directly to queue responses and inspect requests.
#pragma once

#include <aletheia/backend.hpp>

#include <cassert>
#include <cstddef>
#include <expected>
#include <optional>
#include <queue>
#include <span>
#include <string>
#include <string_view>
#include <utility>
#include <vector>

namespace aletheia {

class MockBackend : public IBackend {
    static inline char sentinel = 0;
    std::vector<std::string> captured_;
    std::queue<std::string> responses_;
    // Dedicated queue for the binary frame channel (build_frame_bin /
    // update_frame_bin).  Kept separate from `responses_` so the JSON control
    // plane and the packed-frame byte channel never couple: draining one must
    // not starve the other.
    std::queue<std::vector<std::byte>> frame_responses_;

    // Binary frame-channel exhaustion helper.  Records the `<binary:…>` sentinel
    // (mirroring process()) then pops the next queued packed-frame byte buffer.
    // On an empty queue it RETURNS `std::unexpected(...)` rather than throwing:
    // build_frame_bin / update_frame_bin return `std::expected`, and the Client
    // forwards that result directly, so the error must flow through the value
    // channel to preserve the Result contract.  The op token and message mirror
    // the JSON path and the peer bindings byte-for-byte (#108 unification):
    // ErrorKind::State + "mock backend: no queued response for <op>".
    [[nodiscard]] auto pop_frame(std::string_view op)
        -> std::expected<std::vector<std::byte>, AletheiaError> {
        captured_.emplace_back(op);
        if (frame_responses_.empty()) {
            return std::unexpected(AletheiaError{
                ErrorKind::State, "mock backend: no queued response for " + std::string{op}});
        }
        auto bytes = std::move(frame_responses_.front());
        frame_responses_.pop();
        return bytes;
    }

public:
    void queue_response(std::string json) { responses_.push(std::move(json)); }

    // Queue a packed-frame byte buffer for the next build_frame_bin /
    // update_frame_bin call (the binary frame channel, separate from
    // queue_response's JSON channel).
    void queue_frame_bytes(std::vector<std::byte> bytes) {
        frame_responses_.push(std::move(bytes));
    }

    [[nodiscard]] auto captured() const -> const std::vector<std::string>& { return captured_; }

    [[nodiscard]] auto last_captured() const -> const std::string& {
        assert(!captured_.empty());
        return captured_.back();
    }

    void clear() {
        captured_.clear();
        while (!responses_.empty())
            responses_.pop();
        while (!frame_responses_.empty())
            frame_responses_.pop();
    }

    auto init() -> void* override { return &sentinel; }

    auto process(void* /*state*/, std::string_view input) -> std::string override {
        // Record the request BEFORE the exhaustion check so `captured()` stays
        // populated on the erroring call (cross-binding contract: the starved
        // call is still logged, matching Go / Rust / Python).
        captured_.emplace_back(input);
        if (responses_.empty()) {
            // Exhaustion is a harness misconfiguration, not a wire response:
            // throw rather than fabricate a default (which would silently mask
            // an under-provisioned test).  The op token matches the other
            // bindings byte-for-byte: the `<binary:OP>` sentinel on the binary
            // paths (input IS the sentinel), and the generic "process" on the
            // JSON control-plane path.  ErrorKind::State mirrors Go's kind for
            // the same condition; the message is the cross-binding unified
            // template (#108).
            const std::string op = input.starts_with("<binary:") ? std::string{input} : "process";
            throw AletheiaException(
                AletheiaError{ErrorKind::State, "mock backend: no queued response for " + op});
        }
        auto r = std::move(responses_.front());
        responses_.pop();
        return r;
    }

    // The binary-shim overrides below record a `<binary:…>` sentinel rather than
    // a serialized JSON command.  The real FfiBackend drives every streaming /
    // frame / extract / format operation through the binary FFI; there is no
    // JSON wire for these in production, so a JSON rendering here would be a
    // fiction no real path emits.  The sentinel records *that* a binary call was
    // made; argument values are verified end-to-end by the real-`.so` round-trip
    // tests (e.g. the BRS/ESI passthrough cross-binding test).  Mirrors the
    // Python and Go mock backends exactly (cross-binding mock uniformity).
    auto send_frame_binary(void* state, Timestamp /*ts*/, const CanId& /*id*/, Dlc /*dlc*/,
                           std::span<const std::byte> /*data*/, std::optional<bool> /*brs*/,
                           std::optional<bool> /*esi*/) -> std::string override {
        return process(state, "<binary:sendFrame>");
    }

    auto send_error_binary(void* state, Timestamp /*ts*/) -> std::string override {
        return process(state, "<binary:sendError>");
    }

    auto send_remote_binary(void* state, Timestamp /*ts*/, const CanId& /*id*/)
        -> std::string override {
        return process(state, "<binary:sendRemote>");
    }

    auto start_stream_binary(void* state) -> std::string override {
        return process(state, "<binary:startStream>");
    }

    auto end_stream_binary(void* state) -> std::string override {
        return process(state, "<binary:endStream>");
    }

    auto format_dbc_binary(void* state) -> std::string override {
        return process(state, "<binary:formatDBC>");
    }

    auto extract_signals_binary(void* state, const CanId& /*id*/, Dlc /*dlc*/,
                                std::span<const std::byte> /*data*/) -> std::string override {
        return process(state, "<binary:extractAllSignals>");
    }

    // build_frame_bin / update_frame_bin have no JSON fallback in the Client
    // (it returns backend_->..._bin(...) directly), so the base default —
    // returning ErrorKind::BinaryUnsupported — would leave the mock unable to
    // build/update frames at all.  Override to record the `<binary:…>` sentinel
    // and serve queued packed-frame bytes (or a State-kinded unexpected on an
    // empty queue), matching the Python / Go / Rust mocks (#108).  Argument
    // values are ignored here; the real FfiBackend verifies them end-to-end via
    // the real-`.so` round-trip tests.
    [[nodiscard]] auto build_frame_bin(void* /*state*/, const CanId& /*id*/, Dlc /*dlc*/,
                                       SignalInjection /*signals*/, std::size_t /*expected_bytes*/)
        -> std::expected<std::vector<std::byte>, AletheiaError> override {
        return pop_frame("<binary:buildFrameBin>");
    }

    [[nodiscard]] auto update_frame_bin(void* /*state*/, const CanId& /*id*/, Dlc /*dlc*/,
                                        std::span<const std::byte> /*data*/,
                                        SignalInjection /*signals*/, std::size_t /*expected_bytes*/)
        -> std::expected<std::vector<std::byte>, AletheiaError> override {
        return pop_frame("<binary:updateFrameBin>");
    }

    void close(void* /*state*/) override {}
};

} // namespace aletheia
