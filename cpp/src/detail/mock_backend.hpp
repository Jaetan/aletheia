// Configurable mock backend for testing.
// Tests include this header directly to queue responses and inspect requests.
#pragma once

#include <aletheia/backend.hpp>

#include <format>
#include <queue>
#include <string>
#include <string_view>
#include <variant>
#include <vector>

namespace aletheia {

class MockBackend : public IBackend {
    static inline char sentinel_ = 0;
    std::vector<std::string> captured_;
    std::queue<std::string> responses_;

public:
    void queue_response(std::string json) { responses_.push(std::move(json)); }

    [[nodiscard]] auto captured() const -> const std::vector<std::string>& { return captured_; }

    [[nodiscard]] auto last_captured() const -> const std::string& { return captured_.back(); }

    void clear() {
        captured_.clear();
        while (!responses_.empty())
            responses_.pop();
    }

    auto init() -> void* override { return &sentinel_; }

    auto process(void* /*state*/, std::string_view input) -> std::string override {
        captured_.emplace_back(input);
        if (!responses_.empty()) {
            auto r = std::move(responses_.front());
            responses_.pop();
            return r;
        }
        return R"({"status": "success"})";
    }

    auto send_frame_binary(void* state, Timestamp ts, const CanId& id, Dlc dlc,
                           std::span<const std::byte> data) -> std::string override {
        // Build the equivalent JSON command and delegate to process().
        std::string data_str;
        data_str.reserve(data.size() * 4);
        for (std::size_t i = 0; i < data.size(); ++i) {
            if (i > 0)
                data_str += ',';
            data_str += std::to_string(static_cast<std::uint8_t>(data[i]));
        }
        auto can_id = std::visit([](const auto& v) -> std::uint32_t { return v.value(); }, id);
        auto extended = std::holds_alternative<ExtendedId>(id);
        auto json_cmd = std::format(
            R"({{"type":"data","timestamp":{},"id":{},"extended":{},"dlc":{},"data":[{}]}})",
            ts.count(), can_id, extended ? "true" : "false", dlc.value(), data_str);
        return process(state, json_cmd);
    }

    void close(void* /*state*/) override {}
};

} // namespace aletheia
