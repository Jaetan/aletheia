// SPDX-FileCopyrightText: 2025 Nicolas Pelletier
// SPDX-License-Identifier: BSD-2-Clause
#pragma once

// The step both harnesses end a report's write with: the flush, and the reason
// the report's stream did not take the report.

#include <cerrno>
#include <cstdio>
#include <system_error>

namespace aletheia::bench {

// Flushes `report` and answers why it did not take what it was given, or no
// error when it took it all: the system's reason when the flush fails, and EIO
// when the flush succeeds but the stream's error indicator records an earlier
// failure, such as a write that dropped what it could not write and so left
// the flush nothing to write.
inline auto flush_report(std::FILE* report) -> std::error_code {
    if (std::fflush(report) != 0)
        return {errno, std::generic_category()};
    if (std::ferror(report) != 0)
        return std::make_error_code(std::errc::io_error);
    return {};
}

} // namespace aletheia::bench
