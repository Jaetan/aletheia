// SPDX-FileCopyrightText: 2025 Nicolas Pelletier
// SPDX-License-Identifier: BSD-2-Clause
#pragma once

// The throughput mode: frames per second of streaming, extraction and building.

#include <filesystem>

namespace aletheia::bench {

// The lanes the throughput mode measures: three for each frame family.
inline constexpr int throughput_lanes = 6;

// Lane 0 runs every lane; lane k runs the k-th alone, counted from 1 in the
// order the mode reports them.
void run_throughput(std::filesystem::path const& lib, int num_frames, int num_runs, int warmup,
                    int lane, bool emit_json);

} // namespace aletheia::bench
