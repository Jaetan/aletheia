// SPDX-FileCopyrightText: 2025 Nicolas Pelletier
// SPDX-License-Identifier: BSD-2-Clause
// Configurable mock backend for testing.
// Tests include this header directly to queue responses and inspect requests.
#pragma once

#include <aletheia/backend.hpp>

#include <cassert>
#include <cstddef>
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

public:
    void queue_response(std::string json) { responses_.push(std::move(json)); }

    [[nodiscard]] auto captured() const -> const std::vector<std::string>& { return captured_; }

    [[nodiscard]] auto last_captured() const -> const std::string& {
        assert(!captured_.empty());
        return captured_.back();
    }

    void clear() {
        captured_.clear();
        while (!responses_.empty())
            responses_.pop();
    }

    auto init() -> void* override { return &sentinel; }

    auto process(void* /*state*/, std::string_view input) -> std::string override {
        captured_.emplace_back(input);
        if (!responses_.empty()) {
            auto r = std::move(responses_.front());
            responses_.pop();
            return r;
        }
        // Default reflects the real FFI wire contract: fire-and-forget binary
        // calls (sendFrame / sendError / sendRemote) return {"status":"ack"};
        // everything else returns {"status":"success"}.  Tests that care about
        // the specific status should queue_response() explicitly; the default
        // below only fires when no response is queued.  Matches Python's
        // _ACK_DEFAULT_MARKERS.
        const bool is_fire_and_forget = input.contains("<binary:sendFrame>") ||
                                        input.contains("<binary:sendError>") ||
                                        input.contains("<binary:sendRemote>");
        if (is_fire_and_forget)
            return R"({"status": "ack"})";
        return R"({"status": "success"})";
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

    void close(void* /*state*/) override {}
};

} // namespace aletheia
