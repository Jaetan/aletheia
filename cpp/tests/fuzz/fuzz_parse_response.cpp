// SPDX-FileCopyrightText: 2025 Nicolas Pelletier
// SPDX-License-Identifier: BSD-2-Clause
//
// libFuzzer harness for the JSON response parser (Cat 33b).
// Counterpart of go FuzzParseResponse and python fuzz_parse_response.
//
// Build: requires clang with -fsanitize=fuzzer (configured in CMakeLists.txt
// under the fuzz_targets target group, opt-in via -DALETHEIA_FUZZ=ON).
// Run:   ./build-fuzz/fuzz_parse_response -max_total_time=60 \
//        cpp/tests/fuzz/seed/parse_response/

#include "../../src/detail/json.hpp"

#include <cstddef>
#include <cstdint>
#include <string_view>

extern "C" auto LLVMFuzzerTestOneInput(const uint8_t* data, size_t size) -> int {
    auto input = std::string_view{reinterpret_cast<const char*>(data), size};
    // Each parser entry must not crash on adversarial input.  Errors are
    // expected; the contract is no UB / no exception escape past the API.
    [[maybe_unused]] auto r1 = aletheia::detail::parse_success(input);
    [[maybe_unused]] auto r2 = aletheia::detail::parse_validation(input);
    [[maybe_unused]] auto r3 = aletheia::detail::parse_frame_response(input);
    [[maybe_unused]] auto r4 = aletheia::detail::parse_dbc_response(input);
    [[maybe_unused]] auto r5 = aletheia::detail::parse_parsed_dbc(input);
    [[maybe_unused]] auto r6 = aletheia::detail::parse_event_ack(input);
    return 0;
}
