// SPDX-FileCopyrightText: 2025 Nicolas Pelletier
// SPDX-License-Identifier: BSD-2-Clause

// Functional tests for the C++ CLI (aletheia::run_cli) — the counterpart of
// go/cmd/aletheia/main_test.go. Each subcommand is exercised against a .dbc
// fixture through the real verified FFI core (never a stub); the suite skips
// when libaletheia-ffi.so is unavailable, mirroring the other integration
// tests. ALETHEIA_REPO_ROOT (fixtures) and ALETHEIA_LIB (the .so, consumed by
// run_cli's own resolver) are supplied by ctest via set_tests_properties.

#include <aletheia/cli.hpp>

#include <catch2/catch_test_macros.hpp>
#include <nlohmann/json.hpp>

#include <cstdlib>
#include <filesystem>
#include <fstream>
#include <iostream>
#include <sstream>
#include <stdexcept>
#include <string>
#include <utility>
#include <vector>

namespace {

auto repo_root() -> std::filesystem::path {
    const char* env = std::getenv("ALETHEIA_REPO_ROOT");
    if (env == nullptr || *env == '\0') {
        throw std::runtime_error("ALETHEIA_REPO_ROOT env var not set (ctest sets it)");
    }
    return std::filesystem::path{env};
}

auto lib_available() -> bool {
    if (const char* env = std::getenv("ALETHEIA_LIB"); env != nullptr && *env != '\0') {
        return std::filesystem::exists(env);
    }
    return std::filesystem::exists(repo_root() / "build" / "libaletheia-ffi.so");
}

auto run(std::vector<std::string> args) -> int {
    return aletheia::run_cli(args);
}

// Run a subcommand capturing stdout, so a test can assert the emitted JSON
// shape (not just the exit code).
auto run_capture(std::vector<std::string> args) -> std::pair<int, std::string> {
    std::ostringstream oss;
    auto* old = std::cout.rdbuf(oss.rdbuf());
    const int code = aletheia::run_cli(std::move(args));
    std::cout.rdbuf(old);
    return {code, oss.str()};
}

} // namespace

TEST_CASE("CLI smoke over the real FFI core", "[cli]") {
    if (!lib_available()) {
        SKIP("libaletheia-ffi.so not found — run 'cabal run shake -- build' first");
    }
    const auto dbc = (repo_root() / "examples" / "example.dbc").string();
    CHECK(run({"validate", "--dbc", dbc}) == 0);
    CHECK(run({"validate", "--dbc", dbc, "--json"}) == 0);
    CHECK(run({"signals", "--dbc", dbc}) == 0);
    CHECK(run({"signals", "--dbc", dbc, "--json"}) == 0);
    CHECK(run({"format-dbc", "--dbc", dbc}) == 0);
    CHECK(run({"extract", "--dbc", dbc, "0x100", "102700000A000000"}) == 0);
    // A flag after positionals must still parse (Python argparse parity).
    CHECK(run({"extract", "--dbc", dbc, "0x100", "102700000A000000", "--json"}) == 0);
    const auto mux =
        (repo_root() / "python" / "tests" / "fixtures" / "dbc_corpus" / "multiplexing.dbc")
            .string();
    CHECK(run({"mux-query", "--dbc", mux, "0x64"}) == 0);
    CHECK(run({"mux-query", "--dbc", mux, "0x64", "--json"}) == 0);
    // Selector mode (--mux/--value) + its mismatch error — CoPilot PR #21 review.
    CHECK(run({"mux-query", "--dbc", mux, "0x64", "--mux", "Mode", "--value", "1"}) == 0);
    CHECK(run({"mux-query", "--dbc", mux, "0x64", "--mux", "Mode", "--value", "1", "--json"}) == 0);
    CHECK(run({"mux-query", "--dbc", mux, "0x64", "--mux", "Mode"}) == 2); // --value missing
}

TEST_CASE("extract --json renders signal values as exact rationals, never a lossy float", "[cli]") {
    if (!lib_available()) {
        SKIP("libaletheia-ffi.so not found — run 'cabal run shake -- build' first");
    }
    const auto dbc = (repo_root() / "examples" / "example.dbc").string();
    // EngineSpeed is 16-bit @ factor 0.25; raw 10001 (0x2711, little-endian) =
    // 10001/4 = 2500.25, a non-integer rational -> the exact
    // {"numerator","denominator"} object, never a lossy double like 2500.25.
    // EngineTemp (factor 1, raw 0, offset -40) = -40 -> a bare integer.  Parse
    // the JSON and assert the exact structure (a substring check could
    // false-positive on another field's text).
    auto [code, out] =
        run_capture({"extract", "--dbc", dbc, "0x100", "112700000A000000", "--json"});
    CHECK(code == 0);
    const auto parsed = nlohmann::json::parse(out);
    const auto& values = parsed.at("values");
    CHECK(values.at("EngineSpeed") == nlohmann::json({{"numerator", 10001}, {"denominator", 4}}));
    CHECK(values.at("EngineSpeed").is_object()); // exact rational, never a float
    CHECK(values.at("EngineTemp") == nlohmann::json(-40));
    CHECK(values.at("EngineTemp").is_number_integer()); // integer stays a bare int
}

TEST_CASE("signals text renders a fine-resolution factor exactly via format_rational", "[cli]") {
    if (!lib_available()) {
        SKIP("libaletheia-ffi.so not found — run 'cabal run shake -- build' first");
    }
    // factor 1/8192 = 0.0001220703125 exactly — more significant figures than the
    // old to_double() ostream render kept (it printed "0.00012207").  example.dbc
    // has no such fine factor, so write a dedicated temp DBC.
    const auto dbc = std::filesystem::temp_directory_path() / "aletheia_fine_factor.dbc";
    {
        std::ofstream out{dbc};
        out << "VERSION \"\"\n\nNS_ :\n\nBS_:\n\nBU_:\n\n"
            << "BO_ 1024 FineMsg: 8 ECU4\n"
            << " SG_ FineSignal : 0|16@1+ (0.0001220703125,0) [0|8] \"x\" Vector__XXX\n";
    }
    auto [code, out] = run_capture({"signals", "--dbc", dbc.string()});
    std::error_code ec;
    std::filesystem::remove(dbc, ec);
    CHECK(code == 0);
    CHECK(out.find("x0.0001220703125") != std::string::npos);
}

TEST_CASE("CLI rejects unknown command, deferred check, and empty args", "[cli]") {
    // These fail before touching the FFI core, so they need no .so.
    CHECK(run({"check"}) == 2); // deferred — needs a verified CAN-log reader
    CHECK(run({"bogus"}) == 2);
    CHECK(run({}) == 2); // no subcommand
}
