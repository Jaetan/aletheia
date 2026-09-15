// SPDX-FileCopyrightText: 2025 Nicolas Pelletier
// SPDX-License-Identifier: BSD-2-Clause
//
// libFuzzer harness for the rational-number parser.
// Counterpart of go FuzzParseRationalNumber. Python fuzzes the wire shapes
// that carry rationals (fuzz_parse_response) rather than the number alone.
//
// The Rational parser surface is internal to the json_parse compilation unit
// (parse_rational_number is a static helper), so this harness exercises it
// transitively via parse_validation / parse_dbc_response — wire shapes that
// embed rational numbers in their nested members.
//
// Build/run: see fuzz_parse_response.cpp comment header.

#include "../../src/detail/json.hpp"

#include <cstddef>
#include <cstdint>
#include <string>
#include <string_view>

extern "C" auto LLVMFuzzerTestOneInput(const uint8_t* data, size_t size) -> int {
    // Wrap the fuzzer's input as the two numeric members of a property
    // failure, "property_index" and "timestamp", so the rational-number
    // parser runs on a nested value. Everything around them is constant.
    auto numeric = std::string_view{reinterpret_cast<const char*>(data), size};
    std::string envelope = "{\"status\":\"fails\",\"type\":\"property\","
                           "\"property_index\":";
    envelope.append(numeric);
    envelope.append(",\"timestamp\":");
    envelope.append(numeric);
    envelope.append("}");
    [[maybe_unused]] auto r = aletheia::detail::parse_frame_response(envelope);
    return 0;
}
