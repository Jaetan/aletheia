// SPDX-FileCopyrightText: 2025 Nicolas Pelletier
// SPDX-License-Identifier: BSD-2-Clause
#pragma once

// The client setup every benchmark shares, and the streaming pass the throughput
// and scaling modes both time.

#include "measure.hpp"

#include <aletheia/aletheia.hpp>

#include <filesystem>
#include <span>
#include <stop_token>
#include <vector>

namespace aletheia::bench {

namespace fs = std::filesystem;

// ---------------------------------------------------------------------------
// Client setup shared by every benchmark
// ---------------------------------------------------------------------------

// A benchmark must never time a client whose setup failed, so every setup
// step is checked through require like the timed operations are.
inline auto make_client(const fs::path& lib, const DbcDefinition& dbc) -> AletheiaClient {
    AletheiaClient client(make_ffi_backend(lib));
    require(client.parse_dbc(std::stop_token{}, dbc), "parse_dbc");
    return client;
}

inline auto make_streaming_client(const fs::path& lib, const DbcDefinition& dbc,
                                  std::span<const LtlFormula> properties) -> AletheiaClient {
    auto client = make_client(lib, dbc);
    require(client.set_properties(std::stop_token{}, properties), "set_properties");
    require(client.start_stream(std::stop_token{}), "start_stream");
    return client;
}

inline auto bench_streaming(const fs::path& lib, const DbcDefinition& dbc,
                            std::vector<LtlFormula> properties, CanId id, Dlc dlc,
                            const FramePayload& frame, int num_frames) -> double {
    auto client = make_streaming_client(lib, dbc, properties);
    auto const fps = operations_per_second(num_frames, "send_frame", [&](int i) {
        return client.send_frame(std::stop_token{}, Timestamp{i}, id, dlc, frame);
    });
    require(client.end_stream(std::stop_token{}), "end_stream");
    return fps;
}

} // namespace aletheia::bench
