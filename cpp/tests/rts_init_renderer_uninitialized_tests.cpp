// SPDX-FileCopyrightText: 2025 Nicolas Pelletier
// SPDX-License-Identifier: BSD-2-Clause
//
// The rational renderer and the decimal parser do not start the GHC runtime
// (cpp/src/detail/rts_init.hpp and rational_renderer.cpp). These cases assert
// they are vocal when nothing has started it: a call before a start throws,
// naming the remedy, rather than starting the runtime, which would fix its
// core count before the program chose one, or calling the kernel with the
// runtime down. The allocation count, which only a started runtime keeps,
// answers none.
//
// Must run in its own process, a child of fresh_process_tests, because the GHC
// RTS is process-global: any start in the same process would bring the runtime
// up and defeat the assertion. The listener that starts the runtime for the
// other suites, rts_setup_listener.cpp, is linked into those binaries and not
// into this one.

#include <catch2/catch_test_macros.hpp>
#include <catch2/matchers/catch_matchers.hpp>

#include <aletheia/aletheia.hpp>
#include <aletheia/detail/rational_renderer.hpp>

#include <optional>
#include <string>
#include <string_view>

// The refusal while the runtime is down, after the words naming what the call was doing.
static auto runtime_down(std::string_view reading) -> std::string {
    return "GHC runtime not initialized: call aletheia::start_runtime or open a client before " +
           std::string{reading};
}

TEST_CASE("the renderer is vocal (throws) when the GHC runtime is down",
          "[rational_renderer][rts_init]") {
    REQUIRE_THROWS_WITH(aletheia::detail::format_rational_ffi(22, 7), runtime_down("rendering"));
}

TEST_CASE("Rational::from_decimal is vocal (throws) when the GHC runtime is down",
          "[rational_renderer][rts_init][decimal]") {
    REQUIRE_THROWS_WITH(aletheia::Rational::from_decimal("3.14"), runtime_down("parsing decimals"));
}

TEST_CASE("a runtime-down decimal parse answers on the runtime, not on the literal",
          "[rational_renderer][rts_init][decimal]") {
    // An interior NUL is refused with a Validation error once the runtime is up,
    // but the runtime gate comes first: Rust returns RtsNotInitialized before it
    // looks at the literal, so a runtime-down call here must name the runtime too
    // rather than the input. This pins the order the two bindings share.
    using namespace std::string_view_literals;
    REQUIRE_THROWS_WITH(aletheia::Rational::from_decimal("1\0xyz"sv),
                        runtime_down("parsing decimals"));
}

TEST_CASE("the allocation count answers none while the runtime is down", "[ffi][rts_init]") {
    // Nothing has started the runtime in this process, so no library holds a
    // count to read.
    CHECK(aletheia::allocated_bytes() == std::nullopt);
}
