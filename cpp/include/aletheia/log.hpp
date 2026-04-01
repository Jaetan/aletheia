// SPDX-License-Identifier: BSD-2-Clause
#pragma once

#include <cstdint>
#include <functional>
#include <initializer_list>
#include <source_location>
#include <span>
#include <string_view>
#include <utility>
#include <variant>

namespace aletheia {

// ---------------------------------------------------------------------------
// Structured logging — opt-in, zero-cost when no callback is configured.
//
// Usage:
//   auto logger = aletheia::Logger([](const aletheia::LogRecord& r) {
//       std::cerr << r.event;
//       for (auto& [k, v] : r.fields) { /* format k=v */ }
//   }, aletheia::LogLevel::Info);
//
//   auto client = aletheia::AletheiaClient(std::move(backend), logger);
//
// Default-constructed Logger is a no-op (null callback).
// ---------------------------------------------------------------------------

enum class LogLevel : std::uint8_t { Debug, Info, Warn };

using LogValue = std::variant<std::string_view, std::int64_t, std::uint64_t, double, bool>;
using LogField = std::pair<std::string_view, LogValue>;

struct LogRecord {
    LogLevel level;
    std::string_view event;
    std::span<const LogField> fields;
    std::source_location location;
};

using LogCallback = std::function<void(const LogRecord&)>;

class Logger {
public:
    Logger() = default;

    explicit Logger(LogCallback cb, LogLevel min_level = LogLevel::Debug)
        : cb_(std::move(cb))
        , min_(min_level) {}

    void log(LogLevel lvl, std::string_view event, std::initializer_list<LogField> fields,
             std::source_location loc = std::source_location::current()) const {
        if (!cb_ || lvl < min_)
            return;
        cb_(LogRecord{.level = lvl,
                      .event = event,
                      .fields = std::span<const LogField>{fields.begin(), fields.end()},
                      .location = loc});
    }

    void debug(std::string_view event, std::initializer_list<LogField> fields = {},
               std::source_location loc = std::source_location::current()) const {
        log(LogLevel::Debug, event, fields, loc);
    }

    void info(std::string_view event, std::initializer_list<LogField> fields = {},
              std::source_location loc = std::source_location::current()) const {
        log(LogLevel::Info, event, fields, loc);
    }

    void warn(std::string_view event, std::initializer_list<LogField> fields = {},
              std::source_location loc = std::source_location::current()) const {
        log(LogLevel::Warn, event, fields, loc);
    }

    explicit operator bool() const { return static_cast<bool>(cb_); }

private:
    LogCallback cb_;
    LogLevel min_ = LogLevel::Debug;
};

} // namespace aletheia
