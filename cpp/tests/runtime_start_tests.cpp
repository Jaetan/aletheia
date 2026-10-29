// SPDX-FileCopyrightText: 2025 Nicolas Pelletier
// SPDX-License-Identifier: BSD-2-Clause
//
// `aletheia::start_runtime` starts the kernel's runtime before any client: a
// program starts it, loads checks holding decimals and hands them to a client,
// and a backend made with no count asks for the count running. A call that
// reads a number before the start is refused and keeps nothing: after the
// start the renderer and the parser read the library the runtime started on,
// with no library in the working directory or the environment to find. A
// backend refused for an empty path or a zero count maps no kernel.
//
// A child of fresh_process_tests, a process of its own because the claims are
// about one whose runtime nothing has started; the cases run in the order the
// lane pins (--order decl), the first starting the runtime.

#include <catch2/catch_test_macros.hpp>
#include <catch2/matchers/catch_matchers.hpp>
#include <catch2/matchers/catch_matchers_string.hpp>

#include <aletheia/aletheia.hpp>
#include <aletheia/detail/checked.hpp>
#include <aletheia/detail/rational_renderer.hpp>

#include <cstddef>
#include <filesystem>
#include <fstream>
#include <optional>
#include <stop_token>
#include <string>
#include <utility>
#include <variant>
#include <vector>

#include "repo_root.hpp"
#include "required.hpp"
#include "temp_path.hpp"

using aletheia::test::required;

using Catch::Matchers::StartsWith;

// Whether the process maps the kernel library, read from its own mappings.
static auto kernel_is_mapped() -> bool {
    std::ifstream maps{"/proc/self/maps"};
    for (std::string line; std::getline(maps, line);) {
        if (line.contains("libaletheia-ffi.so")) {
            return true;
        }
    }
    return false;
}

// EngineSpeed's factor 0.25 decodes raw 800 to 200 rpm, past the 199.5 limit.
static constexpr auto k_dbc = R"(VERSION ""

NS_ :

BS_:

BU_: ECU

BO_ 256 EngineStatus: 8 ECU
 SG_ EngineSpeed : 0|16@1+ (0.25,0) [0|8000] "rpm" ECU
)";

static constexpr auto k_checks = R"(checks:
  - name: Speed limit
    signal: EngineSpeed
    condition: never_exceeds
    value: 199.5
    severity: critical
)";

TEST_CASE("a number read before any start is refused, and the start afterwards serves",
          "[runtime]") {
    // Nothing names a library: the variable is cleared and the working
    // directory holds no build, so a reader that searched would find none.
    auto const lib = aletheia::test::repo_root() / "build" / "libaletheia-ffi.so";
    REQUIRE(::unsetenv("ALETHEIA_LIB") == 0);
    aletheia::test::TempPath const nest{aletheia::test::scratch_dir() / "outer" / "inner",
                                        aletheia::test::AsDirectory{}};
    std::filesystem::current_path(nest.path);

    CHECK(aletheia::allocated_bytes() == std::nullopt);
    // A client opened with no library given finds none to open.
    auto const unfound = aletheia::AletheiaClient::open();
    CHECK(aletheia::detail::error_of(unfound).kind() == aletheia::ErrorKind::Ffi);
    CHECK(aletheia::detail::error_of(unfound).text() ==
          "libaletheia-ffi.so not found; set $ALETHEIA_LIB or run 'cabal run shake -- build'");
    CHECK(aletheia::detail::error_of(aletheia::Rational::from_decimal("1.5")).text() ==
          "GHC runtime not initialized: call aletheia::start_runtime or open a "
          "client before parsing decimals");
    CHECK(aletheia::detail::error_of(aletheia::detail::format_rational_ffi(1, 2)).text() ==
          "GHC runtime not initialized: call aletheia::start_runtime or open a "
          "client before rendering");
    // A check built before the start renders its threshold on every read, so the
    // refusal read now is not what a read after the start answers.
    auto const check =
        aletheia::check::signal("Speed").never_exceeds(aletheia::PhysicalValue::of(1, 2));
    CHECK(aletheia::detail::error_of(check.condition_desc()).text() ==
          "GHC runtime not initialized: call aletheia::start_runtime or open a "
          "client before rendering");

    // Zero is outside the bound on every machine; the bound's own figure is the
    // machine's, which the stand-in suite holds whole on its four CPUs.
    auto const refused = aletheia::start_runtime(lib, 0);
    CHECK(aletheia::detail::error_of(refused).kind() == aletheia::ErrorKind::Validation);
    CHECK_THAT(aletheia::detail::error_of(refused).text(),
               StartsWith("core count 0 is outside 1 to "));
    CHECK(aletheia::allocated_bytes() == std::nullopt);

    // An empty path is refused rather than handed to dlopen, which would open
    // the program itself, and a zero count before the library is opened.
    CHECK(aletheia::detail::error_of(aletheia::make_ffi_backend("")).kind() ==
          aletheia::ErrorKind::Validation);
    CHECK(aletheia::detail::error_of(aletheia::make_ffi_backend(lib, 0)).kind() ==
          aletheia::ErrorKind::Validation);
    CHECK_FALSE(kernel_is_mapped());

    CHECK(aletheia::start_runtime(lib, 1) == std::nullopt);
    CHECK(kernel_is_mapped());
    CHECK(aletheia::allocated_bytes().has_value());
    CHECK(aletheia::Rational::from_decimal("1.5") == aletheia::Rational{3, 2});
    CHECK(aletheia::detail::format_rational_ffi(1, 2) == "0.5");
    CHECK(check.condition_desc() == "<= 0.5");
    // With nothing else to find, the search answers the path the start opened.
    CHECK(required(aletheia::find_ffi_library()) == lib);
}

TEST_CASE("default checks holding a decimal, loaded after the start, stream", "[runtime]") {
    auto const lib = aletheia::test::repo_root() / "build" / "libaletheia-ffi.so";
    REQUIRE(aletheia::start_runtime(lib, 1).has_value());
    auto checks = aletheia::load_checks_from_yaml_string(k_checks);
    REQUIRE(checks.has_value());
    auto client = required(aletheia::AletheiaClient::create(
        required(aletheia::make_ffi_backend(lib)), aletheia::Logger{}, std::move(checks).value()));
    REQUIRE(client.parse_dbc_text(std::stop_token{}, k_dbc).has_value());
    REQUIRE(client.add_checks(std::stop_token{}, {}).has_value());
    REQUIRE(client.start_stream(std::stop_token{}).has_value());
    auto const id = aletheia::CanId{aletheia::StandardId::create(0x100).value()};
    auto const dlc = aletheia::Dlc::create(8).value();
    aletheia::FramePayload const data{std::byte{0x20}, std::byte{0x03}, std::byte{0}, std::byte{0},
                                      std::byte{0},    std::byte{0},    std::byte{0}, std::byte{0}};
    auto const result =
        client.send_frame(std::stop_token{}, aletheia::Timestamp{1'000}, id, dlc, data);
    REQUIRE(result.has_value());
    CHECK(std::holds_alternative<aletheia::PropertyBatch>(*result));
}

TEST_CASE("a backend naming no count asks for the count running", "[runtime]") {
    auto const lib = aletheia::test::repo_root() / "build" / "libaletheia-ffi.so";
    CHECK(aletheia::start_runtime(lib, 1) == std::nullopt);
    auto const count_less = required(aletheia::make_ffi_backend(lib));
    CHECK_FALSE(count_less->rts_mismatch_info().has_value());
    // Two is within the CPUs of every machine the suite runs on.
    auto const counted = required(aletheia::make_ffi_backend(lib, 2));
    CHECK(counted->rts_mismatch_info() == std::optional<std::pair<int, int>>{{1, 2}});
    CHECK(required(aletheia::start_runtime(lib, 2)) == std::optional<std::pair<int, int>>{{1, 2}});
}
