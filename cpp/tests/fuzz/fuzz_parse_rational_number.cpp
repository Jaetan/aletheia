// SPDX-FileCopyrightText: 2025 Nicolas Pelletier
// SPDX-License-Identifier: BSD-2-Clause
//
// libFuzzer harness for the rational-number parser.
// Counterpart of go FuzzParseRationalNumber. Python fuzzes the wire shapes
// that carry rationals (fuzz_parse_response) rather than the number alone.
//
// The rational reader is internal to the reply readers (read_rational in
// reply_shape.cpp), so this harness exercises it transitively via
// parse_extraction: an extracted value is the one reply place outside a DBC
// that holds a rational.
//
// Build/run: see fuzz_parse_response.cpp comment header.

#include "../../src/detail/json.hpp"

#include <cstddef>
#include <cstdint>
#include <string>
#include <string_view>

extern "C" auto LLVMFuzzerTestOneInput(uint8_t const* data, size_t size) -> int {
    // Wrap the fuzzer's input as the value of one extracted signal in an
    // otherwise complete reply, so the rational reader runs on a nested value;
    // everything around the number is constant.
    auto const numeric = std::string_view{reinterpret_cast<char const*>(data), size};
    std::string envelope = R"({"status":"success","values":[{"name":"S","value":)";
    envelope.append(numeric);
    envelope.append(R"(}],"errors":[],"absent":[]})");
    [[maybe_unused]] auto const r = aletheia::detail::parse_extraction(envelope);
    return 0;
}
