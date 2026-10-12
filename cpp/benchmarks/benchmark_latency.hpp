// SPDX-FileCopyrightText: 2025 Nicolas Pelletier
// SPDX-License-Identifier: BSD-2-Clause
#pragma once

// The latency mode: the time of each streaming, extraction and building call.

#include <filesystem>

namespace aletheia::bench {

void run_latency(const std::filesystem::path& lib, int ops, int warmup, bool emit_json);

} // namespace aletheia::bench
