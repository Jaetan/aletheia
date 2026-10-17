// SPDX-FileCopyrightText: 2025 Nicolas Pelletier
// SPDX-License-Identifier: BSD-2-Clause
//
// A command holding one long number is refused, and the process that sent it
// lives. The kernel refuses a JSON number whose rational components pass the
// signed 64-bit range, and its refusal reports the measured magnitude up to
// 2^64-1 and that ceiling past it, with "at least" before the ceiling in the
// message. A command of about 100 KB whose one number has 100,001 digits gets
// that refusal. A process of its own, run as a child of fresh_process_tests: a
// kernel that echoes the number whole ends the process that called it.

#include <catch2/catch_test_macros.hpp>

#include <aletheia/backend.hpp>
#include <aletheia/error.hpp>
#include <aletheia/limits.hpp>

#include <cstddef>
#include <cstdint>
#include <format>
#include <limits>
#include <string>

#include "detail/json.hpp"

TEST_CASE("a command holding one long number is refused at the ceiling", "[literal_bound]") {
    // The digits after the leading 1 of the command's one number.
    constexpr std::size_t zeros = 100'000;
    constexpr auto ceiling = std::numeric_limits<std::uint64_t>::max();

    auto const backend = aletheia::make_ffi_backend_from_env();
    auto const state = backend->init();
    auto const command =
        R"({"type": "command", "command": "startStream", "x": 1)" + std::string(zeros, '0') + "}";
    auto const reply = backend->process(state, command);

    auto const result = aletheia::detail::parse_success(reply);
    REQUIRE_FALSE(result.has_value());
    auto const& error = result.error();
    CHECK(error.kind() == aletheia::ErrorKind::InputBoundExceeded);
    CHECK(error.code() == aletheia::ErrorCode::InputBoundExceeded);
    CHECK(error.message() ==
          std::format("rational component magnitude at least {} exceeds limit {}", ceiling,
                      aletheia::max_rational_component_magnitude));
    REQUIRE(error.bound_info().has_value());
    auto const& bound = *error.bound_info();
    CHECK(bound.bound_kind == aletheia::bound_kind_rational_component_magnitude);
    CHECK(bound.observed == ceiling);
    CHECK(bound.limit == aletheia::max_rational_component_magnitude);
    CHECK_FALSE(bound.field.has_value());
}
