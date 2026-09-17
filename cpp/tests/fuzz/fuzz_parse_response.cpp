// SPDX-FileCopyrightText: 2025 Nicolas Pelletier
// SPDX-License-Identifier: BSD-2-Clause
//
// libFuzzer harness for the JSON response parser.
// Counterpart of go FuzzParseResponse and python fuzz_parse_response.
//
// Build and run, for every harness in this directory.  -fsanitize=fuzzer,
// which cpp/CMakeLists.txt adds to each of them behind the ALETHEIA_FUZZ
// option, links its own runtime, so they need a directory of their own:
//   cmake -B build-fuzz -DALETHEIA_FUZZ=ON \
//       -DCMAKE_C_COMPILER=clang-23 -DCMAKE_CXX_COMPILER=clang++-23
//   cmake --build build-fuzz --target fuzz_parse_response
//   mkdir -p build-fuzz/corpus/parse_response
//   ./build-fuzz/fuzz_parse_response -max_total_time=60 \
//       build-fuzz/corpus/parse_response tests/fuzz/seed/parse_response/
// libFuzzer writes every input it finds into the FIRST directory it is given
// and only reads the rest, so the corpus directory comes first and the seed
// directory second.  Given the seed directory alone it writes there, which
// leaves hundreds of hash-named files among seeds that are named for the case
// each one covers.  The corpus directory lives under build-fuzz/ because
// .gitignore already ignores that tree, and libFuzzer refuses to start unless
// it exists, hence the mkdir.  Every path is from cpp/, as in the build file's
// other lanes, and the lines were run from there to check them.

#include "../../src/detail/json.hpp"

#include <cstddef>
#include <cstdint>
#include <string_view>

extern "C" auto LLVMFuzzerTestOneInput(const uint8_t* data, size_t size) -> int {
    auto const input = std::string_view{reinterpret_cast<const char*>(data), size};
    // Each parser entry must not crash on adversarial input.  Errors are
    // expected; the contract is no UB / no exception escape past the API.
    [[maybe_unused]] auto const r1 = aletheia::detail::parse_success(input);
    [[maybe_unused]] auto const r2 = aletheia::detail::parse_validation(input);
    [[maybe_unused]] auto const r3 = aletheia::detail::parse_frame_response(input);
    [[maybe_unused]] auto const r4 = aletheia::detail::parse_dbc_response(input);
    [[maybe_unused]] auto const r5 = aletheia::detail::parse_parsed_dbc(input);
    [[maybe_unused]] auto const r6 = aletheia::detail::parse_event_ack(input);
    return 0;
}
