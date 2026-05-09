// SPDX-License-Identifier: BSD-2-Clause
//
// libFuzzer harness for DBC JSON parser (R18 cluster 5 — Cat 33b).
// Counterpart of go FuzzParseDBCJSON and python fuzz_dbc_to_json.
//
// Build/run: see fuzz_parse_response.cpp comment header.

#include "../../src/detail/json.hpp"

#include <cstddef>
#include <cstdint>
#include <string_view>

extern "C" auto LLVMFuzzerTestOneInput(const uint8_t* data, size_t size) -> int {
    auto input = std::string_view{reinterpret_cast<const char*>(data), size};
    // The DBC body parser receives wire JSON; assert no UB / no leak / no
    // exception escape on adversarial input.
    [[maybe_unused]] auto r = aletheia::detail::parse_dbc_response(input);
    [[maybe_unused]] auto p = aletheia::detail::parse_parsed_dbc(input);
    return 0;
}
