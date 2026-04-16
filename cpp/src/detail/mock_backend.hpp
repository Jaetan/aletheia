// SPDX-License-Identifier: BSD-2-Clause
// Configurable mock backend for testing.
// Tests include this header directly to queue responses and inspect requests.
#pragma once

#include "json.hpp"

#include <aletheia/backend.hpp>

#include <cassert>
#include <queue>
#include <string>
#include <string_view>
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
        // Default reflects the real FFI wire contract: fire-and-forget events
        // (sendFrame / sendError / sendRemote per StreamState.agda:81-82)
        // return {"status":"ack"}; everything else returns {"status":"success"}.
        // Tests that care about the specific status should queue_response()
        // explicitly; the default below only fires when no response is queued.
        const bool is_fire_and_forget =
            input.find(R"("command":"sendFrame")") != std::string_view::npos ||
            input.find(R"("command":"sendError")") != std::string_view::npos ||
            input.find(R"("command":"sendRemote")") != std::string_view::npos ||
            input.find(R"("type":"data")") != std::string_view::npos ||
            input.find(R"("type":"error")") != std::string_view::npos ||
            input.find(R"("type":"remote")") != std::string_view::npos;
        if (is_fire_and_forget)
            return R"({"status": "ack"})";
        return R"({"status": "success"})";
    }

    auto send_frame_binary(void* state, Timestamp ts, const CanId& id, Dlc dlc,
                           std::span<const std::byte> data) -> std::string override {
        return process(state, detail::serialize_send_frame(ts, id, dlc, data));
    }

    auto send_error_binary(void* state, Timestamp ts) -> std::string override {
        return process(state, detail::serialize_send_error(ts));
    }

    auto send_remote_binary(void* state, Timestamp ts, const CanId& id) -> std::string override {
        return process(state, detail::serialize_send_remote(ts, id));
    }

    void close(void* /*state*/) override {}
};

} // namespace aletheia
