// SPDX-FileCopyrightText: 2025 Nicolas Pelletier
// SPDX-License-Identifier: BSD-2-Clause
//
// The rational renderer releases every string the kernel hands it: a render,
// and a decimal parse's refusal. A process of its own, because the renderer
// calls the library the runtime started on, which happens once per process,
// and the one library whose releases can be read is the recording kernel,
// which counts them; the suite that shares a process with the real library
// cannot point the renderer at it. For the same reason the allocation count is
// read here, the recording kernel being the library this process's runtime
// started on.

#include <catch2/catch_test_macros.hpp>
#include <catch2/matchers/catch_matchers.hpp>
#include <catch2/matchers/catch_matchers_string.hpp>

#include <aletheia/aletheia.hpp>
#include <aletheia/detail/rational_renderer.hpp>

#include <cstdint>
#include <dlfcn.h>
#include <filesystem>

#include "loaded_library.hpp"

TEST_CASE("the renderer frees the strings the kernel hands it", "[rational_renderer]") {
    // A backend on the stand-in starts the runtime on it, its runtime entry a
    // no-op, so the renderer calls the stand-in.
    const std::filesystem::path stand_in{ALETHEIA_TEST_RECORDING_KERNEL};
    auto const backend = aletheia::make_ffi_backend(stand_in);
    const aletheia::test::LoadedLibrary handle{dlopen(stand_in.c_str(), RTLD_NOW | RTLD_NOLOAD)};
    REQUIRE(handle != nullptr);
    using CountFn = int (*)();
    // NOLINTNEXTLINE(cppcoreguidelines-pro-type-reinterpret-cast)
    auto* const frees = reinterpret_cast<CountFn>(dlsym(handle.get(), "aletheia_test_free_count"));
    REQUIRE(frees != nullptr);

    auto before = frees();
    CHECK(aletheia::detail::format_rational_ffi(22, 7) == "22/7");
    CHECK(frees() == before + 1);

    before = frees();
    auto const parsed = aletheia::detail::parse_decimal_ffi("1.5");
    REQUIRE_FALSE(parsed.has_value());
    CHECK_THAT(parsed.error(), Catch::Matchers::ContainsSubstring("parse_decimal"));
    CHECK(frees() == before + 1);
}

TEST_CASE("the allocation count comes back whole from the library that started the runtime",
          "[ffi]") {
    // The recording kernel answers its count with 2^63 plus the reads made
    // before, and nothing in this process reads it earlier, so the reads give
    // 2^63 and then one more only when each reached the entry and all 64 bits
    // came back: a read that keeps fewer bits reads another number. Every
    // backend this process makes is on the stand-in, so it is the one the
    // runtime started on.
    auto const backend =
        aletheia::make_ffi_backend(std::filesystem::path{ALETHEIA_TEST_RECORDING_KERNEL});
    auto const first = aletheia::allocated_bytes();
    auto const second = aletheia::allocated_bytes();
    REQUIRE(first.has_value());
    REQUIRE(second.has_value());
    CHECK(first.value() == (std::uint64_t{1} << 63U));
    CHECK(second.value() == (std::uint64_t{1} << 63U) + 1);
}
