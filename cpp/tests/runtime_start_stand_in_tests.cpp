// SPDX-FileCopyrightText: 2025 Nicolas Pelletier
// SPDX-License-Identifier: BSD-2-Clause
//
// The core count a start or a backend asks is held to one through the CPUs the
// process may use, as the runtime of the library counts them, and the answer
// names the bound. The recording kernel counts four CPUs whatever the machine
// and its runtime entry is a no-op, so the runtime reads as started on the
// count asked; it renders a rational as its two components, which shows the
// renderer reads the library the runtime started on.
//
// A child of fresh_process_tests, a process of its own because the runtime
// starts once per process; the cases run in the order the lane pins
// (--order decl).

#include <catch2/catch_test_macros.hpp>
#include <catch2/matchers/catch_matchers.hpp>

#include <aletheia/aletheia.hpp>
#include <aletheia/detail/rational_renderer.hpp>

#include <filesystem>
#include <optional>
#include <string>
#include <utility>

TEST_CASE("a count outside one to the CPUs the runtime counts is refused, naming the bound",
          "[runtime]") {
    const std::filesystem::path stand_in{ALETHEIA_TEST_RECORDING_KERNEL};
    for (auto const cores : {0, 5}) {
        auto const refusal = "core count " + std::to_string(cores) +
                             " is outside 1 to 4, the CPUs this process may use";
        CHECK_THROWS_WITH(aletheia::start_runtime(stand_in, cores), refusal);
        CHECK_THROWS_WITH(aletheia::make_ffi_backend(stand_in, cores), refusal);
    }
    CHECK(aletheia::allocated_bytes() == std::nullopt);
}

TEST_CASE("a start's count is the running one for every later start and backend", "[runtime]") {
    const std::filesystem::path stand_in{ALETHEIA_TEST_RECORDING_KERNEL};
    CHECK_FALSE(aletheia::start_runtime(stand_in, 2).has_value());
    CHECK_FALSE(aletheia::make_ffi_backend(stand_in)->rts_mismatch_info().has_value());
    CHECK(aletheia::make_ffi_backend(stand_in, 1)->rts_mismatch_info() ==
          std::optional<std::pair<int, int>>{{2, 1}});
    CHECK(aletheia::start_runtime(stand_in, 4) == std::optional<std::pair<int, int>>{{2, 4}});
    CHECK(aletheia::detail::format_rational_ffi(1, 2) == "1/2");
}
