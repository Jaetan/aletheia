// SPDX-FileCopyrightText: 2025 Nicolas Pelletier
// SPDX-License-Identifier: BSD-2-Clause
#pragma once

// The scaling mode: how the streaming rate and the DBC load time grow with
// their input.

#include <filesystem>

namespace aletheia::bench {

void run_scaling(const std::filesystem::path& lib, int num_runs, bool quick, bool emit_json);

} // namespace aletheia::bench
