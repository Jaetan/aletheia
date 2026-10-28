// SPDX-FileCopyrightText: 2025 Nicolas Pelletier
// SPDX-License-Identifier: BSD-2-Clause
//
// Standalone program run by unit_tests_validation.cpp: asks each stand-in
// kernel that lacks an entry for a runtime start and for a backend, and prints
// each answer. A library lacking an entry is refused before any entry is
// called, so the program answers; a check that let a null entry through ends
// it by a signal, which the test reads as its own failed assertion, where the
// same call made in the test's process would end that process instead.
//
// Exit codes: 0 = every answer the refusal naming the entry missing; 1 = an
// answer that is not, or an exception; 2 = an argument, which the program takes
// none of.

#include <aletheia/backend.hpp>
#include <aletheia/detail/checked.hpp>
#include <aletheia/error.hpp>

#include <array>
#include <cstddef>
#include <cstdio>
#include <filesystem>
#include <print>
#include <span>
#include <string>
#include <string_view>

#if !defined(ALETHEIA_TEST_SYMBOLLESS_LIB) || !defined(ALETHEIA_TEST_ABI_ONLY_LIB)
#error "the stand-ins' paths are compile definitions of the build"
#endif

namespace {

// A stand-in and the entry its refusal names, the first one it lacks.
struct Lacking {
    std::string_view library;
    std::string_view entry;
};

constexpr std::array lacking{
    Lacking{.library = ALETHEIA_TEST_SYMBOLLESS_LIB, .entry = "aletheia_abi_version"},
    Lacking{.library = ALETHEIA_TEST_ABI_ONLY_LIB, .entry = "hs_init_with_rtsopts"},
};

} // namespace

// Whether `answer` is the refusal naming the entry `stand_in` lacks, printing
// what `call` answered.
template<typename T>
static auto refused(std::string_view call, Lacking const& stand_in,
                    aletheia::Result<T> const& answer) -> bool {
    if (answer) {
        std::println(stderr, "{} of {}: answered a value", call, stand_in.library);
        return false;
    }
    auto const& error = aletheia::detail::error_of(answer);
    std::println("{} of {}: {}", call, stand_in.library, error.text());
    return error.kind() == aletheia::ErrorKind::Ffi &&
           error.text().contains("dlsym failed for " + std::string{stand_in.entry});
}

static auto run(std::span<char* const> args) -> int {
    if (args.size() > 1) {
        std::println(stderr, "missing_entry_workload: takes no argument, got '{}'", args[1]);
        return 2;
    }
    bool all_refused = true;
    for (auto const& stand_in : lacking) {
        std::filesystem::path const library{stand_in.library};
        all_refused =
            refused("start_runtime", stand_in, aletheia::start_runtime(library, 1)) && all_refused;
        all_refused = refused("make_ffi_backend", stand_in, aletheia::make_ffi_backend(library)) &&
                      all_refused;
    }
    return all_refused ? 0 : 1;
}

// The test reads this program's exit code, so nothing leaves main: an escaping
// exception would end it by a signal, which the test reads as a null entry
// called rather than as the error it is.
auto main(int argc, char** argv) -> int {
    try {
        return run(std::span{argv, static_cast<std::size_t>(argc)});
    } catch (...) {
        return 1;
    }
}
