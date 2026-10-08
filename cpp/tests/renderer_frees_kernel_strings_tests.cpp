// SPDX-FileCopyrightText: 2025 Nicolas Pelletier
// SPDX-License-Identifier: BSD-2-Clause
//
// The rational renderer releases every string the kernel hands it: a render,
// and a decimal parse's refusal. A process of its own, because the renderer
// loads its library once per process and keeps it, and the one library whose
// releases can be read is the recording kernel, which counts them; the suite
// that shares a process with the real library cannot point the renderer at it.

#include <catch2/catch_test_macros.hpp>
#include <catch2/matchers/catch_matchers.hpp>
#include <catch2/matchers/catch_matchers_string.hpp>

#include <aletheia/aletheia.hpp>
#include <aletheia/detail/rational_renderer.hpp>

#include <dlfcn.h>
#include <filesystem>

#include "loaded_library.hpp"

TEST_CASE("the renderer frees the strings the kernel hands it", "[rational_renderer]") {
    // The renderer reads the variable before any registered path, and a
    // backend on the stand-in marks the runtime up without starting one: its
    // runtime entry is a no-op.
    const std::filesystem::path stand_in{ALETHEIA_TEST_RECORDING_KERNEL};
    REQUIRE(::setenv("ALETHEIA_LIB", stand_in.c_str(), 1) == 0);
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
