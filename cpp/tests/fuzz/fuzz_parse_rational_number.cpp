// SPDX-FileCopyrightText: 2025 Nicolas Pelletier
// SPDX-License-Identifier: BSD-2-Clause
//
// libFuzzer harness for Rational number parser (Cat 33b).
// Counterpart of go FuzzParseRationalNumber and python
// fuzz_parse_rational_number.
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
    // Wrap fuzzer input as a numeric value inside a {"propertyIndex": …,
    // "timestamp": …} envelope so the rational-number parser exercises the
    // nested-object code path.  The rest of the JSON is a constant prefix
    // around the fuzz-controlled numeric payload.
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
