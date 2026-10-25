// SPDX-FileCopyrightText: 2025 Nicolas Pelletier
// SPDX-License-Identifier: BSD-2-Clause
//
// A library that answers the decimal entry with failure and no error envelope
// is a wire fault, a Protocol error as in every binding. The null kernel the
// build makes beside the library answers so, and answers its allocation count
// with zero, which the binding hands on as it came. A process of its own,
// because the runtime starts once per process, and the parser and the count
// read the library it started on; for the same reason the backend that
// started it is the first to register its path for the search.

#include <catch2/catch_test_macros.hpp>

#include <aletheia/aletheia.hpp>

#include <cstdint>
#include <filesystem>
#include <optional>
#include <string_view>

TEST_CASE("a decimal failure without an envelope is a protocol error", "[rational_renderer]") {
    // A backend on the stand-in starts the runtime on it, its runtime entry a
    // no-op, so the parser calls the stand-in.
    const std::filesystem::path stand_in{ALETHEIA_TEST_NULL_KERNEL};
    auto const backend = aletheia::make_ffi_backend(stand_in);
    REQUIRE(backend != nullptr);
    try {
        static_cast<void>(aletheia::Rational::from_decimal("1"));
        FAIL("the null kernel answers no rational");
    } catch (const aletheia::AletheiaException& e) {
        CHECK(e.kind() == aletheia::ErrorKind::Protocol);
        CHECK(e.code() == aletheia::ErrorCode::Unknown);
        CHECK(std::string_view{e.what()} == "aletheia_parse_decimal failed without an error");
    }
}

TEST_CASE("a backend that starts the runtime registers its library for the search", "[ffi]") {
    // Nothing else in this process registers a path before the backend above,
    // and with the variable unset the registered path is the search's first
    // answer, ahead of the build directories around the working directory.
    const std::filesystem::path stand_in{ALETHEIA_TEST_NULL_KERNEL};
    auto const backend = aletheia::make_ffi_backend(stand_in);
    REQUIRE(::unsetenv("ALETHEIA_LIB") == 0);
    CHECK(aletheia::find_ffi_library() == stand_in);
}

TEST_CASE("the allocation count is the kernel's answer, zero included", "[ffi]") {
    auto const backend =
        aletheia::make_ffi_backend(std::filesystem::path{ALETHEIA_TEST_NULL_KERNEL});
    CHECK(aletheia::allocated_bytes() == std::optional<std::uint64_t>{0});
}
