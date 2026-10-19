// SPDX-FileCopyrightText: 2025 Nicolas Pelletier
// SPDX-License-Identifier: BSD-2-Clause
//
// A library that answers the decimal entry with failure and no error envelope
// is a wire fault, a Protocol error as in every binding. The null kernel the
// build makes beside the library answers so. A process of its own, because the
// renderer loads its library once per process and keeps it.

#include <catch2/catch_test_macros.hpp>

#include <aletheia/aletheia.hpp>

#include <filesystem>
#include <string_view>

TEST_CASE("a decimal failure without an envelope is a protocol error", "[rational_renderer]") {
    // The renderer reads the variable before any registered path, and a
    // backend on the stand-in marks the runtime up without starting one: its
    // runtime entry is a no-op.
    const std::filesystem::path stand_in{ALETHEIA_TEST_NULL_KERNEL};
    REQUIRE(::setenv("ALETHEIA_LIB", stand_in.c_str(), 1) == 0);
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
