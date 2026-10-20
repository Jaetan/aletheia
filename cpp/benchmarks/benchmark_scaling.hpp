// SPDX-FileCopyrightText: 2025 Nicolas Pelletier
// SPDX-License-Identifier: BSD-2-Clause
#pragma once

// The scaling mode: how the streaming rate grows with its input, and how a
// DBC load's time and allocated bytes grow with its input, the bytes being
// what the `load scaling` check gates.

#include <filesystem>

namespace aletheia::bench {

void run_scaling(const std::filesystem::path& lib, int num_runs, bool quick, bool emit_json);

} // namespace aletheia::bench
