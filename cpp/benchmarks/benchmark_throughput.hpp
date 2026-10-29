// SPDX-FileCopyrightText: 2025 Nicolas Pelletier
// SPDX-License-Identifier: BSD-2-Clause
#pragma once

// The throughput mode: frames per second of streaming, extraction and building.

#include <filesystem>

namespace aletheia::bench {

void run_throughput(std::filesystem::path const& lib, int num_frames, int num_runs, int warmup,
                    bool emit_json);

} // namespace aletheia::bench
